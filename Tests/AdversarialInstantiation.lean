module

public import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch
public import L4YAML.Output.Emitter
public import L4YAML.Output.Events
public import L4YAML.Parser.Composition
public import L4YAML.Parser.IndexedComposition
public import L4YAML.Proofs.Parser.ParserGrammableBase
public import L4YAML.Proofs.Parser.TokenGrammar
public import L4YAML.Proofs.Serialization.TokenEvents
public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Proofs.Serialization.TraceOf.FlowWalk
public import L4YAML.Proofs.Scanner.RegisterWitness
public import L4YAML.Proofs.Serialization.ScannerShape
public import L4YAML.Proofs.Scanner.DocStartLive
public import L4YAML.Proofs.Scanner.FlowAdjacency
public import L4YAML.Proofs.Output.AlignProofs
public import L4YAML.Proofs.Scanner.FlowAdjacencyIx
public import L4YAML.Proofs.Serialization.TraceOf.Leaves
public import L4YAML.Proofs.Serialization.TraceOf.Document
public import L4YAML.Proofs.Serialization.RefLex
public import L4YAML.Proofs.Serialization.SerializationWellFormed
public import L4YAML.Proofs.Serialization.TokenEvents
public import L4YAML.Proofs.Serialization.ParseCheckFrom
public import L4YAML.Proofs.Parser.TokenGrammar
public import L4YAML.Proofs.Serialization.TokenEvents
public import Tests.VerifiedResult

@[expose] public section Blanket

/-!
# Adversarial Instantiation Tests

Computational verification of sorry'd theorem statements by systematically
instantiating them on adversarial inputs. Detects false claims before
investing proof effort.

See `DOCS.md` ("Adversarial instantiation") for methodology and triage.

## Priority 1 — Theorems 9g, 9h (emitList / emitPairList characterization)

These theorems claim properties about the filtered token sequence produced by
scanning emitter output. A bug was previously caught here where inner-level
`flowEntry` tokens (inside nested brackets) were incorrectly required to
satisfy the outer-level characterization.

After the `flowBracketBalance` fix, we re-verify with deeply nested,
mixed-nesting, and previously-failing inputs.
-/

open L4YAML L4YAML.Scanner L4YAML.Emit L4YAML.TokenParser L4YAML.Proofs.ParserGrammable
open Tests

namespace Tests.AdversarialInstantiation

/-! ## Infrastructure -/

/-- Compute flowBracketDelta for a token value. -/
def fbd (t : YamlToken) : Int :=
  match t with
  | .flowSequenceStart | .flowMappingStart => 1
  | .flowSequenceEnd | .flowMappingEnd => -1
  | _ => 0

/-- Compute bracket balance over a token array slice [lo, hi). -/
def bracketBal (tokens : Array (Positioned YamlToken)) (lo hi : Nat) : Int :=
  let slice := tokens.toList.drop lo |>.take (hi - lo)
  slice.foldl (fun acc t => acc + fbd t.val) 0

/-- Check if a token value is a "content start" (scalar, flowSeqStart, or flowMapStart). -/
def isContentStart (t : YamlToken) : Bool :=
  match t with
  | .scalar _ _ => true
  | .flowSequenceStart => true
  | .flowMappingStart => true
  | _ => false

/-- Pretty-print a token for debugging. -/
def tokStr (t : YamlToken) : String :=
  match t with
  | .streamStart => "streamStart"
  | .streamEnd => "streamEnd"
  | .placeholder => "placeholder"
  | .flowSequenceStart => "["
  | .flowSequenceEnd => "]"
  | .flowMappingStart => "{"
  | .flowMappingEnd => "}"
  | .flowEntry => ","
  | .key => "key"
  | .value => ":"
  | .scalar c _ => s!"scalar({c})"
  | .blockSequenceStart => "blockSeqStart"
  | .blockMappingStart => "blockMapStart"
  | .blockEnd => "blockEnd"
  | .blockEntry => "blockEntry"
  | .documentStart => "docStart"
  | .documentEnd => "docEnd"
  | .versionDirective m n => s!"%YAML {m}.{n}"
  | .tagDirective h p => s!"%TAG {h} {p}"
  | .anchor n => s!"&{n}"
  | .alias n => s!"*{n}"
  | .tag h s => s!"tag({h},{s})"
  | .comment t => s!"#{t}"

/-- Scan a string and return filtered tokens. -/
def scanEmitted (input : String) : IO (Array (Positioned YamlToken)) := do
  match scanFiltered input with
  | .ok tokens => return tokens
  | .error e => throw (IO.Error.userError s!"scan failed: {repr e}")

/-! ## Value constructors -/

/-- Scalar value. -/
def sv (content : String) : YamlValue :=
  .scalar { content, style := .plain }

/-- Flow sequence value. -/
def seqv (items : List YamlValue) : YamlValue :=
  .sequence .flow items.toArray

/-- Flow mapping value. -/
def mapv (pairs : List (YamlValue × YamlValue)) : YamlValue :=
  .mapping .flow pairs.toArray

/-! ## 9g: emitList body characterization

  For sequence emission: `"[" ++ emitList items ++ "]"`
  Filtered tokens: streamStart, `[`, <body>, `]`, streamEnd
  Body = first token is content-start;
         every outer-level `,` is followed by content-start
-/

/-- Check 9g characterization for a given list of items. -/
def check9g (state : IO.Ref TestCollector)
    (label : String) (items : List YamlValue) : IO Unit := do
  let emitted := "[" ++ emit.emitList items ++ "]"
  let tokens ← scanEmitted emitted

  if tokens.size < 5 then
    checkM state s!"{label}: size≥5" false s!"size={tokens.size}"
    return

  check state s!"{label}: streamStart" (tokens[0]!.val == .streamStart)
  check state s!"{label}: flowSeqStart" (tokens[1]!.val == .flowSequenceStart)
  check state s!"{label}: flowSeqEnd" (tokens[tokens.size - 2]!.val == .flowSequenceEnd)
  check state s!"{label}: streamEnd" (tokens[tokens.size - 1]!.val == .streamEnd)

  let bodyStart : Nat := 2
  let bodyEnd : Nat := tokens.size - 2

  if items.isEmpty then return

  -- (1) First body token is content-start
  let firstTok := tokens[bodyStart]!.val
  checkM state s!"{label}: first body is content-start"
    (isContentStart firstTok) s!"got {tokStr firstTok}"

  -- (2) Every outer-level flowEntry is followed by content-start
  for _h : i in [bodyStart:bodyEnd] do
    let tok := tokens[i]!.val
    if tok == .flowEntry then
      let bal := bracketBal tokens bodyStart i
      if bal == 0 then
        if i + 1 < bodyEnd then
          let nextTok := tokens[i + 1]!.val
          checkM state s!"{label}: outer flowEntry@{i} → content-start"
            (isContentStart nextTok) s!"bal=0, next={tokStr nextTok}"
        else
          checkM state s!"{label}: outer flowEntry@{i} → has next"
            false "no token after flowEntry"

/-! ## 9h: emitPairList body characterization

  For mapping emission: `"{" ++ emitPairList pairs ++ "}"`
  Filtered tokens: streamStart, `{`, <body>, `}`, streamEnd
  Body = first token is `.key`;
         every outer-level `,` is followed by `.key`
-/

/-- Check 9h characterization for a given list of pairs. -/
def check9h (state : IO.Ref TestCollector)
    (label : String) (pairs : List (YamlValue × YamlValue)) : IO Unit := do
  let emitted := "{" ++ emit.emitPairList pairs ++ "}"
  let tokens ← scanEmitted emitted

  if tokens.size < 5 then
    checkM state s!"{label}: size≥5" false s!"size={tokens.size}"
    return

  check state s!"{label}: streamStart" (tokens[0]!.val == .streamStart)
  check state s!"{label}: flowMapStart" (tokens[1]!.val == .flowMappingStart)
  check state s!"{label}: flowMapEnd" (tokens[tokens.size - 2]!.val == .flowMappingEnd)
  check state s!"{label}: streamEnd" (tokens[tokens.size - 1]!.val == .streamEnd)

  let bodyStart : Nat := 2
  let bodyEnd : Nat := tokens.size - 2

  if pairs.isEmpty then return

  -- (1) First body token is .key
  let firstTok := tokens[bodyStart]!.val
  checkM state s!"{label}: first body is .key"
    (firstTok == .key) s!"got {tokStr firstTok}"

  -- (2) Every outer-level flowEntry is followed by .key
  for _h : i in [bodyStart:bodyEnd] do
    let tok := tokens[i]!.val
    if tok == .flowEntry then
      let bal := bracketBal tokens bodyStart i
      if bal == 0 then
        if i + 1 < bodyEnd then
          let nextTok := tokens[i + 1]!.val
          checkM state s!"{label}: outer flowEntry@{i} → .key"
            (nextTok == .key) s!"bal=0, next={tokStr nextTok}"
        else
          checkM state s!"{label}: outer flowEntry@{i} → has next"
            false "no token after flowEntry"

/-! ## Test Suites -/

def test9g (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "9g: emitList_body_filtered_characterization"

  -- Flat sequences
  check9g state "flat-1" [sv "a"]
  check9g state "flat-2" [sv "a", sv "b"]
  check9g state "flat-3" [sv "a", sv "b", sv "c"]

  -- 1-level nesting
  check9g state "nest1-seq" [seqv [sv "a", sv "b"], sv "c"]
  check9g state "nest1-map" [mapv [(sv "k", sv "v")], sv "c"]

  -- 2-level nesting
  check9g state "nest2" [seqv [seqv [sv "a"]]]
  check9g state "nest2-multi" [seqv [seqv [sv "a"]], sv "b"]

  -- Mixed sequences/mappings
  check9g state "mixed-1" [mapv [(sv "k", sv "v")], seqv [sv "a"]]
  check9g state "mixed-2" [sv "plain", seqv [sv "a", sv "b"], mapv [(sv "x", sv "y")]]

  -- Previously-failing case (nested mappings inside sequences)
  check9g state "prev-fail-1" [mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")]]
  check9g state "prev-fail-2"
    [mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")], sv "after"]

  -- Deep nesting
  check9g state "deep-3" [seqv [seqv [seqv [sv "deep"]]]]
  check9g state "deep-mixed"
    [mapv [(sv "a", seqv [mapv [(sv "b", sv "c")]])]]

  -- Edge cases
  check9g state "empty-scalar" [sv ""]
  check9g state "special-chars" [sv "hello \"world\"", sv "line1\nline2"]
  check9g state "many-items" [sv "a", sv "b", sv "c", sv "d", sv "e", sv "f"]

def test9h (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "9h: emitPairList_body_filtered_characterization"

  -- Single pair
  check9h state "pair-1" [(sv "k", sv "v")]

  -- Multiple pairs
  check9h state "pairs-2" [(sv "k1", sv "v1"), (sv "k2", sv "v2")]
  check9h state "pairs-3" [(sv "a", sv "1"), (sv "b", sv "2"), (sv "c", sv "3")]

  -- Previously-failing analogue
  check9h state "prev-fail-map" [(sv "k1", sv "v1"), (sv "k2", sv "v2")]

  -- Nested values in mappings
  check9h state "nested-seq-val" [(sv "k", seqv [sv "a", sv "b"])]
  check9h state "nested-map-val" [(sv "k", mapv [(sv "inner_k", sv "inner_v")])]
  check9h state "nested-seq-key" [(seqv [sv "a"], sv "v")]

  -- Mixed nested structures
  check9h state "map-in-map" [(sv "a", mapv [(sv "b", sv "c")])]
  check9h state "seq-in-map"
    [(sv "items", seqv [sv "x", sv "y"]), (sv "count", sv "2")]
  check9h state "complex"
    [(sv "data", seqv [mapv [(sv "id", sv "1")], mapv [(sv "id", sv "2")]]),
     (sv "meta", mapv [(sv "ver", sv "1.0")])]

  -- Deep nesting in mapping values
  check9h state "deep-val" [(sv "k", seqv [seqv [seqv [sv "deep"]]])]
  check9h state "multi-deep"
    [(sv "a", seqv [seqv [sv "1"]]),
     (sv "b", mapv [(sv "c", mapv [(sv "d", sv "e")])])]

  -- Edge cases
  check9h state "empty-key" [(sv "", sv "v")]
  check9h state "empty-val" [(sv "k", sv "")]
  check9h state "special-chars-kv" [(sv "hello \"world\"", sv "line1\nline2")]
  check9h state "many-pairs"
    [(sv "a", sv "1"), (sv "b", sv "2"), (sv "c", sv "3"),
     (sv "d", sv "4"), (sv "e", sv "5"), (sv "f", sv "6")]

/-! ## Collection entry point -/

/-! ### Priority 2 — Theorems 9c, 9d (emit round-trip content equivalence)

These theorems claim that for any `YamlValue v`:
- 9c (sequences): `parseYamlRaw (emit (.sequence style items ..)) = .ok raw_docs` with
  `raw_docs.size = 1` implies `contentEq (.sequence ..) (composed[0]!.value) = true`
- 9d (mappings): Same for `.mapping`

We test the full pipeline: `emit v → parseYaml → compose → contentEq v result`.
This covers both the sequence and mapping cases, plus scalars as base cases.
-/

/-- Check that `emit v` round-trips through the parser with content preserved.
    Tests: (1) parsing succeeds, (2) exactly 1 document, (3) contentEq holds. -/
def checkRoundTrip (state : IO.Ref TestCollector)
    (label : String) (v : YamlValue) : IO Unit := do
  let emitted := emit v
  match parseYamlRaw emitted with
  | .error e =>
    checkM state s!"{label}: parse succeeds" false s!"parse error: {repr e}"
  | .ok raw_docs =>
    check state s!"{label}: parse succeeds" true
    checkM state s!"{label}: exactly 1 doc" (raw_docs.size == 1)
      s!"got {raw_docs.size} docs"
    if raw_docs.size == 1 then
      let composed := raw_docs.map YamlDocument.compose
      let result := composed[0]!.value
      let eq := contentEq v result
      if !eq then
        -- Show what we got for debugging
        let emittedResult := emit result
        checkM state s!"{label}: contentEq" false
          s!"emitted='{emitted}' parsed_back='{emittedResult}'"
      else
        check state s!"{label}: contentEq" true

/-! ## Priority 2 Test Suites -/

def test9cd (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "9c/9d: emit round-trip content equivalence"

  -- Scalars (base case for both 9c and 9d)
  checkRoundTrip state "scalar-plain" (sv "hello")
  checkRoundTrip state "scalar-empty" (sv "")
  checkRoundTrip state "scalar-escape" (sv "with \"escape\"")
  checkRoundTrip state "scalar-newline" (sv "line1\nline2")
  checkRoundTrip state "scalar-tab" (sv "col1\tcol2")
  checkRoundTrip state "scalar-backslash" (sv "path\\to\\file")
  checkRoundTrip state "scalar-unicode" (sv "hello \u0000world")
  checkRoundTrip state "scalar-colon-space" (sv "key: value")
  checkRoundTrip state "scalar-hash" (sv "not # a comment")
  checkRoundTrip state "scalar-brackets" (sv "[not, a, sequence]")
  checkRoundTrip state "scalar-braces" (sv "{not: a, mapping: true}")

  -- 9c: Sequences
  setCategory state "9c: emit_roundtrip_sequence_content_eq"

  -- Empty
  checkRoundTrip state "seq-empty" (seqv [])

  -- Flat
  checkRoundTrip state "seq-1" (seqv [sv "a"])
  checkRoundTrip state "seq-2" (seqv [sv "a", sv "b"])
  checkRoundTrip state "seq-3" (seqv [sv "a", sv "b", sv "c"])

  -- Nested sequences
  checkRoundTrip state "seq-nested-1" (seqv [seqv [sv "a", sv "b"], sv "c"])
  checkRoundTrip state "seq-nested-2" (seqv [seqv [seqv [sv "deep"]]])
  checkRoundTrip state "seq-nested-3" (seqv [seqv [seqv [seqv [sv "deeper"]]]])

  -- Sequences with mappings
  checkRoundTrip state "seq-with-map" (seqv [mapv [(sv "k", sv "v")], sv "c"])
  checkRoundTrip state "seq-with-multi-map"
    (seqv [mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")]])

  -- Mixed nesting
  checkRoundTrip state "seq-mixed"
    (seqv [sv "plain", seqv [sv "a", sv "b"], mapv [(sv "x", sv "y")]])
  checkRoundTrip state "seq-deep-mixed"
    (seqv [mapv [(sv "a", seqv [mapv [(sv "b", sv "c")]])]])

  -- Edge cases
  checkRoundTrip state "seq-empty-scalars" (seqv [sv "", sv "", sv ""])
  checkRoundTrip state "seq-special-chars"
    (seqv [sv "hello \"world\"", sv "line1\nline2", sv "tab\there"])
  checkRoundTrip state "seq-many"
    (seqv [sv "a", sv "b", sv "c", sv "d", sv "e", sv "f", sv "g", sv "h"])

  -- Previously-failing patterns (from Priority 1: inner commas)
  checkRoundTrip state "seq-prev-fail"
    (seqv [mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")], sv "after"])

  -- 9d: Mappings
  setCategory state "9d: emit_roundtrip_mapping_content_eq"

  -- Empty
  checkRoundTrip state "map-empty" (mapv [])

  -- Flat
  checkRoundTrip state "map-1" (mapv [(sv "k", sv "v")])
  checkRoundTrip state "map-2" (mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")])
  checkRoundTrip state "map-3"
    (mapv [(sv "a", sv "1"), (sv "b", sv "2"), (sv "c", sv "3")])

  -- Nested mappings
  checkRoundTrip state "map-nested-1" (mapv [(sv "outer", mapv [(sv "inner", sv "val")])])
  checkRoundTrip state "map-nested-2"
    (mapv [(sv "a", mapv [(sv "b", mapv [(sv "c", sv "deep")])])])

  -- Mappings with sequences
  checkRoundTrip state "map-with-seq" (mapv [(sv "items", seqv [sv "x", sv "y"])])
  checkRoundTrip state "map-with-nested-seq"
    (mapv [(sv "data", seqv [seqv [sv "a", sv "b"], seqv [sv "c"]])])

  -- Mixed nesting
  checkRoundTrip state "map-mixed"
    (mapv [(sv "items", seqv [sv "x", sv "y"]), (sv "count", sv "2")])
  checkRoundTrip state "map-complex"
    (mapv [(sv "data", seqv [mapv [(sv "id", sv "1")], mapv [(sv "id", sv "2")]]),
           (sv "meta", mapv [(sv "ver", sv "1.0")])])

  -- Deep nesting
  checkRoundTrip state "map-deep-val"
    (mapv [(sv "k", seqv [seqv [seqv [sv "deep"]]])])
  checkRoundTrip state "map-multi-deep"
    (mapv [(sv "a", seqv [seqv [sv "1"]]),
           (sv "b", mapv [(sv "c", mapv [(sv "d", sv "e")])])])

  -- Edge cases
  checkRoundTrip state "map-empty-key" (mapv [(sv "", sv "v")])
  checkRoundTrip state "map-empty-val" (mapv [(sv "k", sv "")])
  checkRoundTrip state "map-special-chars"
    (mapv [(sv "hello \"world\"", sv "line1\nline2")])
  checkRoundTrip state "map-many"
    (mapv [(sv "a", sv "1"), (sv "b", sv "2"), (sv "c", sv "3"),
           (sv "d", sv "4"), (sv "e", sv "5"), (sv "f", sv "6")])

  -- Sequence keys in mappings (stress test for key complexity)
  checkRoundTrip state "map-seq-key" (mapv [(seqv [sv "a", sv "b"], sv "v")])
  checkRoundTrip state "map-map-key"
    (mapv [(mapv [(sv "inner", sv "key")], sv "v")])

  -- 5-level deep nesting
  checkRoundTrip state "deep-5"
    (seqv [seqv [seqv [seqv [seqv [sv "bottom"]]]]])
  checkRoundTrip state "map-deep-5"
    (mapv [(sv "1", mapv [(sv "2", mapv [(sv "3",
      mapv [(sv "4", mapv [(sv "5", sv "bottom")])])])])])

  -- Cross: deeply nested mixed structures
  checkRoundTrip state "cross-nested"
    (seqv [mapv [(sv "key", seqv [mapv [(sv "inner", seqv [sv "a", sv "b"])]])]])

/-! ## Priority 3 — Theorems 9a, 9b (parser fuel sufficiency)

These theorems claim that `parseStream` succeeds on emitter output. The key sorry is
in `scanFiltered_emitSeq_nonempty_structure` / `scanFiltered_emitMap_nonempty_structure`:
the fuel bound `4 * tokens.size + 4` suffices for `parseNode` / `parseFlowSequence` /
`parseFlowMapping` to succeed on the token stream produced by the emitter.

We test:
1. **Correctness:** `parseStream (scanFiltered (emit v))` returns `.ok docs` with `docs.size = 1`
2. **Tightness:** `parseNode` at pos=1 with fuel `4*N+3` (one less than `parseDocument` uses) —
   does it still work or is the bound exactly tight?
3. **Scaling:** Report token counts to verify fuel scales with input complexity
-/

/-- Check parser fuel sufficiency for an emitted value.
    Returns `(tokensSize, fuelUsed, tightFuelWorks)`. -/
def checkFuelSufficiency (state : IO.Ref TestCollector)
    (label : String) (v : YamlValue) : IO Unit := do
  let emitted := emit v
  -- Step 1: Scan to get tokens
  match scanFiltered emitted with
  | .error e =>
    checkM state s!"{label}: scan succeeds" false s!"scan error: {repr e}"
  | .ok tokens =>
    check state s!"{label}: scan succeeds" true
    let n := tokens.size
    let fuel := 4 * n + 4

    -- Step 2: parseStream with standard fuel (4*N+4 inside parseDocument)
    match parseStream tokens with
    | .error e =>
      checkM state s!"{label}: parseStream ok (fuel={fuel}, N={n})" false
        s!"parse error: {repr e}"
    | .ok docs =>
      check state s!"{label}: parseStream ok (fuel={fuel}, N={n})" true
      checkM state s!"{label}: exactly 1 doc" (docs.size == 1)
        s!"got {docs.size} docs"

    -- Step 3: Tightness — call parseNode directly at pos=1 with fuel-1
    if n ≥ 2 then
      let ps1 : ParseState := { tokens := tokens, pos := 1 }
      let tightFuel := 4 * n + 3  -- one less than parseDocument uses
      match parseNode ps1 tightFuel with
      | .ok _ =>
        check state s!"{label}: tight fuel {tightFuel} also works" true
      | .error _ =>
        -- This is informational — if this fails, 4*N+4 is exactly tight
        check state s!"{label}: tight fuel {tightFuel} fails (bound is tight!)" true

/-! ## Priority 3 Test Suites -/

def test9ab (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "9a: parseStream_emitSequence fuel sufficiency"

  -- Empty sequence (base case — already proven, sanity check)
  checkFuelSufficiency state "seq-empty" (seqv [])

  -- Single element
  checkFuelSufficiency state "seq-1" (seqv [sv "a"])

  -- Two elements (minimal non-trivial)
  checkFuelSufficiency state "seq-2" (seqv [sv "a", sv "b"])

  -- Many elements (wide: stress the loop fuel)
  checkFuelSufficiency state "seq-8"
    (seqv [sv "a", sv "b", sv "c", sv "d", sv "e", sv "f", sv "g", sv "h"])
  checkFuelSufficiency state "seq-12"
    (seqv [sv "a", sv "b", sv "c", sv "d", sv "e", sv "f",
           sv "g", sv "h", sv "i", sv "j", sv "k", sv "l"])

  -- Nested sequences (depth: stress recursive parseNode calls)
  checkFuelSufficiency state "seq-depth-2" (seqv [seqv [sv "a", sv "b"]])
  checkFuelSufficiency state "seq-depth-3" (seqv [seqv [seqv [sv "a"]]])
  checkFuelSufficiency state "seq-depth-4" (seqv [seqv [seqv [seqv [sv "a"]]]])
  checkFuelSufficiency state "seq-depth-5"
    (seqv [seqv [seqv [seqv [seqv [sv "a"]]]]])
  checkFuelSufficiency state "seq-depth-6"
    (seqv [seqv [seqv [seqv [seqv [seqv [sv "a"]]]]]])

  -- Wide + deep (both dimensions at once)
  checkFuelSufficiency state "seq-wide-deep"
    (seqv [seqv [sv "a", sv "b", sv "c"],
           seqv [sv "d", sv "e"],
           seqv [sv "f"]])
  checkFuelSufficiency state "seq-deep-wide"
    (seqv [seqv [seqv [sv "a", sv "b"]],
           seqv [seqv [sv "c", sv "d"]]])

  -- Sequences containing mappings (mixed nesting)
  checkFuelSufficiency state "seq-with-map"
    (seqv [mapv [(sv "k", sv "v")]])
  checkFuelSufficiency state "seq-with-multi-map"
    (seqv [mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")]])
  checkFuelSufficiency state "seq-with-nested-map"
    (seqv [mapv [(sv "outer", mapv [(sv "inner", sv "val")])]])
  checkFuelSufficiency state "seq-map-seq"
    (seqv [mapv [(sv "items", seqv [sv "x", sv "y"])]])

  -- Previously-failing patterns from P1 (inner commas at depth > 0)
  checkFuelSufficiency state "seq-prev-fail-1"
    (seqv [mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")], sv "after"])
  checkFuelSufficiency state "seq-prev-fail-2"
    (seqv [seqv [sv "a", sv "b"], mapv [(sv "c", sv "d"), (sv "e", sv "f")]])

  -- Deep mixed nesting (worst case for fuel)
  checkFuelSufficiency state "seq-deep-mixed-1"
    (seqv [mapv [(sv "a", seqv [mapv [(sv "b", seqv [sv "c"])]])]])
  checkFuelSufficiency state "seq-deep-mixed-2"
    (seqv [seqv [mapv [(sv "k", seqv [sv "v1", sv "v2"])],
                 mapv [(sv "j", mapv [(sv "m", sv "n")])]]])

  -- Extreme depth: 7 levels
  checkFuelSufficiency state "seq-depth-7"
    (seqv [seqv [seqv [seqv [seqv [seqv [seqv [sv "bottom"]]]]]]])

  -- Extreme width: 16 elements
  checkFuelSufficiency state "seq-width-16"
    (seqv (List.range 16 |>.map (fun i => sv s!"item{i}")))

  setCategory state "9b: parseStream_emitMapping fuel sufficiency"

  -- Empty mapping (base case)
  checkFuelSufficiency state "map-empty" (mapv [])

  -- Single entry
  checkFuelSufficiency state "map-1" (mapv [(sv "k", sv "v")])

  -- Two entries
  checkFuelSufficiency state "map-2" (mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")])

  -- Many entries (wide)
  checkFuelSufficiency state "map-6"
    (mapv [(sv "a", sv "1"), (sv "b", sv "2"), (sv "c", sv "3"),
           (sv "d", sv "4"), (sv "e", sv "5"), (sv "f", sv "6")])
  checkFuelSufficiency state "map-10"
    (mapv (List.range 10 |>.map (fun i => (sv s!"k{i}", sv s!"v{i}"))))

  -- Nested mappings (depth)
  checkFuelSufficiency state "map-depth-2"
    (mapv [(sv "outer", mapv [(sv "inner", sv "val")])])
  checkFuelSufficiency state "map-depth-3"
    (mapv [(sv "a", mapv [(sv "b", mapv [(sv "c", sv "val")])])])
  checkFuelSufficiency state "map-depth-4"
    (mapv [(sv "a", mapv [(sv "b", mapv [(sv "c", mapv [(sv "d", sv "val")])])])])
  checkFuelSufficiency state "map-depth-5"
    (mapv [(sv "1", mapv [(sv "2", mapv [(sv "3",
      mapv [(sv "4", mapv [(sv "5", sv "val")])])])])])

  -- Mappings with sequence values
  checkFuelSufficiency state "map-with-seq"
    (mapv [(sv "items", seqv [sv "x", sv "y"])])
  checkFuelSufficiency state "map-with-nested-seq"
    (mapv [(sv "data", seqv [seqv [sv "a", sv "b"], seqv [sv "c"]])])

  -- Mappings with complex keys
  checkFuelSufficiency state "map-seq-key"
    (mapv [(seqv [sv "a", sv "b"], sv "v")])
  checkFuelSufficiency state "map-map-key"
    (mapv [(mapv [(sv "inner", sv "key")], sv "v")])

  -- Many entries with complex values
  checkFuelSufficiency state "map-multi-complex"
    (mapv [(sv "items", seqv [sv "a", sv "b", sv "c"]),
           (sv "config", mapv [(sv "debug", sv "true"), (sv "level", sv "3")]),
           (sv "name", sv "test")])

  -- Deep mixed nesting
  checkFuelSufficiency state "map-deep-mixed-1"
    (mapv [(sv "a", seqv [mapv [(sv "b", seqv [sv "c", sv "d"])]])])
  checkFuelSufficiency state "map-deep-mixed-2"
    (mapv [(sv "x", mapv [(sv "y", seqv [mapv [(sv "z", sv "w")]])])])

  -- Wide + deep
  checkFuelSufficiency state "map-wide-deep"
    (mapv [(sv "a", seqv [sv "1", sv "2"]),
           (sv "b", mapv [(sv "c", sv "3")]),
           (sv "d", seqv [mapv [(sv "e", sv "4")]])])

  -- Extreme depth: 6 levels
  checkFuelSufficiency state "map-depth-6"
    (mapv [(sv "1", mapv [(sv "2", mapv [(sv "3",
      mapv [(sv "4", mapv [(sv "5", mapv [(sv "6", sv "val")])])])])])])

  -- Extreme width: 16 entries
  checkFuelSufficiency state "map-width-16"
    (mapv (List.range 16 |>.map (fun i => (sv s!"k{i}", sv s!"v{i}"))))

  -- Cross-type stress tests
  setCategory state "9a/9b: cross-type fuel stress"

  -- Alternating seq/map nesting
  checkFuelSufficiency state "cross-alt-1"
    (seqv [mapv [(sv "k", seqv [mapv [(sv "j", sv "v")]])]])
  checkFuelSufficiency state "cross-alt-2"
    (mapv [(sv "k", seqv [mapv [(sv "j", seqv [sv "a", sv "b"])]])])

  -- Wide at multiple levels
  checkFuelSufficiency state "cross-wide-multi"
    (seqv [mapv [(sv "a", sv "1"), (sv "b", sv "2")],
           mapv [(sv "c", sv "3"), (sv "d", sv "4")],
           seqv [sv "e", sv "f", sv "g"]])

  -- Complex realistic structure
  checkFuelSufficiency state "cross-realistic"
    (mapv [(sv "users",
            seqv [mapv [(sv "name", sv "alice"),
                        (sv "roles", seqv [sv "admin", sv "user"])],
                  mapv [(sv "name", sv "bob"),
                        (sv "roles", seqv [sv "user"])]]),
           (sv "version", sv "2.0")])

/-! ## Priority 4 — Theorem 9e (scanner prefix invariant)

Theorem `scanNextToken_prefix_and_sk_inv` claims that for each `scanNextToken` step
from `s` to `s'`, given any prefix index `n ≤ s.tokens.size`:

1. **Prefix preservation:** `∀ i < n, s'.tokens[i] = s.tokens[i]`
2. **Disjunctive SK/EK output invariant:** Either `s'.simpleKey.possible → s'.simpleKey.tokenIndex ≥ n`,
   or `s'.explicitKeyLine = none`.

**Corrected precondition**: The precondition uses `s.simpleKey.possible → tokenIndex ≥ n`
(NO disjunction). The original theorem had `∨ s.explicitKeyLine = none` in the precondition,
which was FALSE: adversarial testing found that when `ek = none` but `sk.possible = true`
and `sk.tokenIndex < n`, the scanner overwrites `tokens[sk.tokenIndex]` (placeholder → key),
violating prefix preservation. Counterexample: `"a: b"` at step 1.

The disjunction is correct in the OUTPUT (conclusion) because flow close operations restore
simpleKeys from the stack with tokenIndex potentially < n, but in those cases ek is none.

**Chain-level tests** verify that with `n₀` fixed at the initial state, both prefix
preservation and the strong SK invariant hold across the full scanning chain.
-/

/-- Check the prefix-and-sk invariant for one scanNextToken step.
    Uses the maximum valid n for which the precondition
    `sk.possible → sk.tokenIndex ≥ n` holds (the CORRECTED precondition
    after removing the false `∨ ek = none` disjunction).
    Returns `(n, prefixOk, skInvOk, origPrecondFails)`.
    `skInvOk` checks the disjunctive OUTPUT: `(sk'.possible → tokenIndex ≥ n) ∨ ek'=none`.
    `origPrecondFails` = true when the original (broken) theorem's disjunction
    would give a larger n that causes prefix violation. -/
def checkPrefixSkStep (s s' : ScannerState) :
    Nat × Bool × Bool × Bool :=
  -- Max n where precondition (sk.possible → sk.tokenIndex ≥ n) holds:
  let n :=
    if s.simpleKey.possible then
      min s.simpleKey.tokenIndex s.tokens.size
    else
      s.tokens.size

  -- The n the original (broken) theorem would use (including second disjunct):
  let nOrig :=
    if s.explicitKeyLine.isNone then
      s.tokens.size  -- second disjunct allows max n
    else
      n  -- same as corrected

  -- 1. Prefix preservation for corrected n
  let prefixOk := (List.range n).all fun i =>
    if h : i < s.tokens.size then
      if h' : i < s'.tokens.size then
        s'.tokens[i] == s.tokens[i]
      else false
    else true

  -- 2. Disjunctive output invariant: (sk'.possible → tokenIndex ≥ n) ∨ ek'=none
  let skInvOk :=
    (if s'.simpleKey.possible then s'.simpleKey.tokenIndex ≥ n else true) ||
    s'.explicitKeyLine.isNone

  -- 3. Does the original (broken) precondition give a DIFFERENT (larger) n?
  let origPrecondFails := nOrig > n

  (n, prefixOk, skInvOk, origPrecondFails)

/-- Drive scanning step-by-step through an input string, checking the invariant at each step.
    Returns the number of steps taken and whether any check failed. -/
def checkScanInvariant (state : IO.Ref TestCollector)
    (label : String) (input : String) : IO Unit := do
  let s0 := ScannerState.mk' input
  let s0 := s0.emit .streamStart
  -- Handle BOM
  let s0 := match s0.peek? with
    | some '\uFEFF' => s0.advance
    | _ => s0
  let fuel := (input.utf8ByteSize + 1) * 4
  let mut s := s0
  let mut step := 0
  let mut allPrefixOk := true
  let mut allSkInvOk := true
  let mut lastFailInfo := ""
  let mut minN := 999999  -- track minimum n across steps (diagnostic)
  let mut maxN := 0       -- track maximum n across steps (diagnostic)
  let mut origDisjunctIssues := 0  -- count steps where ∨ek=none gives bad n
  for _ in [:fuel] do
    match scanNextToken s with
    | .error e =>
      checkM state s!"{label}: no scan error" false s!"step {step}: {repr e}"
      return
    | .ok none =>
      -- End of input
      break
    | .ok (some s') =>
      let (n, prefixOk, skInvOk, origPrecondFails) := checkPrefixSkStep s s'
      if n < minN then minN := n
      if n > maxN then maxN := n
      if !prefixOk then
        allPrefixOk := false
        lastFailInfo := s!"prefix fail at step {step}, n={n}, s.tokens={s.tokens.size}→s'.tokens={s'.tokens.size}, sk.possible={s.simpleKey.possible}, sk.tokenIndex={s.simpleKey.tokenIndex}, ek={repr s.explicitKeyLine}"
      if !skInvOk then
        allSkInvOk := false
        lastFailInfo := s!"sk_inv fail at step {step}: sk.possible={s'.simpleKey.possible}, sk.tokenIndex={s'.simpleKey.tokenIndex}, n={n}, explicitKeyLine={repr s'.explicitKeyLine}"
      if origPrecondFails then
        origDisjunctIssues := origDisjunctIssues + 1
      s := s'
      step := step + 1
  checkM state s!"{label}: prefix preserved ({step} steps, n∈[{minN},{maxN}])" allPrefixOk lastFailInfo
  checkM state s!"{label}: sk/ek output invariant ({step} steps)" allSkInvOk lastFailInfo
  -- Report steps where the original theorem's ∨ek=none disjunct would allow
  -- a larger n that causes prefix violation (counterexample to original statement)
  if origDisjunctIssues > 0 then
    check state s!"{label}: original h_cond disjunct issues ({origDisjunctIssues} steps)" true

/-- Check the chain-level invariant: fix `n₀` at the initial state and verify that
    1. prefix preservation (`∀ i < n₀, s_k.tokens[i] = s₀.tokens[i]`) holds at EVERY step
    2. strong SK invariant (`sk_k.possible → tokenIndex_k ≥ n₀`) holds at EVERY step
    This tests whether `ScanChain_preserves_raw_prefix` can work without the
    `∨ explicitKeyLine = none` disjunction. -/
def checkChainInvariant (state : IO.Ref TestCollector)
    (label : String) (input : String) : IO Unit := do
  let s0 := ScannerState.mk' input
  let s0 := s0.emit .streamStart
  let s0 := match s0.peek? with
    | some '\uFEFF' => s0.advance
    | _ => s0
  -- Fix n₀ at start: max n where sk.possible → tokenIndex ≥ n₀
  let n₀ :=
    if s0.simpleKey.possible then
      min s0.simpleKey.tokenIndex s0.tokens.size
    else
      s0.tokens.size
  let fuel := (input.utf8ByteSize + 1) * 4
  let mut s := s0
  let mut step := 0
  let mut allPrefixOk := true
  let mut allStrongSkOk := true
  let mut lastFailInfo := ""
  for _ in [:fuel] do
    match scanNextToken s with
    | .error e =>
      checkM state s!"{label} chain: no scan error" false s!"step {step}: {repr e}"
      return
    | .ok none => break
    | .ok (some s') =>
      -- Chain prefix: s'.tokens[i] = s₀.tokens[i] for i < n₀
      let chainPrefixOk := (List.range n₀).all fun i =>
        if h : i < s0.tokens.size then
          if h' : i < s'.tokens.size then
            s'.tokens[i] == s0.tokens[i]
          else false
        else true
      -- Strong SK at every intermediate state
      let strongSkOk :=
        if s'.simpleKey.possible then s'.simpleKey.tokenIndex ≥ n₀ else true
      if !chainPrefixOk then
        allPrefixOk := false
        lastFailInfo := s!"chain prefix fail at step {step}, n₀={n₀}, s'.tokens.size={s'.tokens.size}"
      if !strongSkOk then
        allStrongSkOk := false
        lastFailInfo := s!"chain sk fail at step {step}: sk'.possible={s'.simpleKey.possible}, sk'.tokenIndex={s'.simpleKey.tokenIndex}, n₀={n₀}"
      s := s'
      step := step + 1
  checkM state s!"{label} chain: prefix preserved (n₀={n₀}, {step} steps)" allPrefixOk lastFailInfo
  checkM state s!"{label} chain: strong sk invariant (n₀={n₀}, {step} steps)" allStrongSkOk lastFailInfo

/-! ## Priority 4 Test Suites -/

def test9e (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "9e: scanNextToken_prefix_and_sk_inv"

  -- Flow indicators (exercises dispatchFlowIndicators)
  checkScanInvariant state "flow-seq-empty" "[]"
  checkScanInvariant state "flow-seq-1" "[a]"
  checkScanInvariant state "flow-seq-2" "[a, b]"
  checkScanInvariant state "flow-seq-3" "[a, b, c]"
  checkScanInvariant state "flow-map-empty" "{}"
  checkScanInvariant state "flow-map-1" "{a: b}"
  checkScanInvariant state "flow-map-2" "{a: b, c: d}"

  -- Nested flow (exercises simpleKeyStack save/restore)
  checkScanInvariant state "flow-nested-1" "[[a, b], c]"
  checkScanInvariant state "flow-nested-2" "[{a: b}, c]"
  checkScanInvariant state "flow-nested-3" "{a: [b, c]}"
  checkScanInvariant state "flow-nested-deep" "[[[a]]]"
  checkScanInvariant state "flow-nested-mixed" "[{a: [b, {c: d}]}, e]"

  -- Quoted scalars (exercises scanFlowScalar / scanDoubleQuotedScalar)
  checkScanInvariant state "dquoted" "\"hello world\""
  checkScanInvariant state "squoted" "'hello world'"
  checkScanInvariant state "dquoted-escape" "\"line1\\nline2\""
  checkScanInvariant state "dquoted-unicode" "\"\\u0041\""
  checkScanInvariant state "flow-dquoted" "[\"a\", \"b\"]"
  checkScanInvariant state "flow-squoted" "['a', 'b']"

  -- Block scalars (exercises scanBlockScalar)
  checkScanInvariant state "block-literal" "|\n  line1\n  line2"
  checkScanInvariant state "block-folded" ">\n  line1\n  line2"

  -- Block sequences (exercises scanBlockEntry)
  checkScanInvariant state "block-seq-1" "- a"
  checkScanInvariant state "block-seq-2" "- a\n- b"
  checkScanInvariant state "block-seq-3" "- a\n- b\n- c"
  checkScanInvariant state "block-seq-nested" "- - a\n  - b"

  -- Block mappings (exercises scanKey / scanValue)
  checkScanInvariant state "block-map-1" "a: b"
  checkScanInvariant state "block-map-2" "a: b\nc: d"
  checkScanInvariant state "block-map-nested" "a:\n  b: c"
  checkScanInvariant state "block-map-deep" "a:\n  b:\n    c: d"

  -- Explicit keys (exercises explicit key path — sets explicitKeyLine)
  checkScanInvariant state "explicit-key" "? a\n: b"
  checkScanInvariant state "explicit-key-flow" "{? a: b}"

  -- Document markers (exercises scanDocumentStart / scanDocumentEnd)
  checkScanInvariant state "doc-start" "---\na: b"
  checkScanInvariant state "doc-end" "a: b\n..."
  checkScanInvariant state "multi-doc" "---\na: b\n...\n---\nc: d"

  -- Directives (exercises scanDirective)
  checkScanInvariant state "yaml-directive" "%YAML 1.2\n---\na: b"
  checkScanInvariant state "tag-directive" "%TAG !t! tag:example.com,2000:\n---\na: b"

  -- Mixed flow/block
  checkScanInvariant state "block-with-flow-val" "items: [a, b, c]"
  checkScanInvariant state "block-with-flow-map" "config: {debug: true}"
  checkScanInvariant state "block-seq-flow-vals" "- [a, b]\n- {c: d}"

  -- Comments (exercises comment scanning)
  checkScanInvariant state "comment-line" "# comment\na: b"
  checkScanInvariant state "comment-inline" "a: b # comment"
  checkScanInvariant state "comment-only" "# just a comment"

  -- Anchors and aliases (exercises anchor/alias scanning)
  checkScanInvariant state "anchor" "&anc a"
  checkScanInvariant state "anchor-alias" "&anc a\n*anc"
  checkScanInvariant state "anchor-flow" "[&anc a, *anc]"

  -- Tags (exercises tag scanning)
  checkScanInvariant state "tag-named" "!!str hello"
  checkScanInvariant state "tag-verbatim" "!<tag:yaml.org,2002:str> hello"

  -- Empty/minimal inputs
  checkScanInvariant state "empty" ""
  checkScanInvariant state "whitespace-only" "   "
  checkScanInvariant state "newline-only" "\n"
  checkScanInvariant state "just-scalar" "hello"

  -- Plain scalars with tricky chars
  checkScanInvariant state "plain-colon-space" "a : b"
  checkScanInvariant state "plain-multiword" "hello world"

  -- Emitter output (exercises exact token patterns from theorems 9a/9b)
  checkScanInvariant state "emit-seq" (emit (seqv [sv "a", sv "b"]))
  checkScanInvariant state "emit-map" (emit (mapv [(sv "k", sv "v")]))
  checkScanInvariant state "emit-nested"
    (emit (seqv [mapv [(sv "k", seqv [sv "a", sv "b"])]]))
  checkScanInvariant state "emit-deep"
    (emit (seqv [seqv [seqv [seqv [sv "a"]]]]))
  checkScanInvariant state "emit-wide"
    (emit (mapv [(sv "a", sv "1"), (sv "b", sv "2"), (sv "c", sv "3"),
                 (sv "d", sv "4"), (sv "e", sv "5"), (sv "f", sv "6")]))
  checkScanInvariant state "emit-complex"
    (emit (mapv [(sv "users",
                  seqv [mapv [(sv "name", sv "alice"),
                              (sv "roles", seqv [sv "admin", sv "user"])],
                        mapv [(sv "name", sv "bob"),
                              (sv "roles", seqv [sv "user"])]]),
                 (sv "version", sv "2.0")]))

  -- Stress: many steps (deep block nesting)
  checkScanInvariant state "deep-block"
    "a:\n  b:\n    c:\n      d:\n        e:\n          f: val"

  -- Stress: wide block sequence
  checkScanInvariant state "wide-block-seq"
    "- a\n- b\n- c\n- d\n- e\n- f\n- g\n- h\n- i\n- j"

  -- Stress: mixed everything
  checkScanInvariant state "kitchen-sink"
    "%YAML 1.2\n---\nitems:\n  - name: \"alice\"\n    roles: [admin, user]\n  - name: 'bob'\n    tags:\n      ? key1\n      : val1\n...\n---\nsecond: doc"

  -- Chain-level invariant tests (fixed n₀ across all steps)
  checkChainInvariant state "flow-seq-2" "[a, b]"
  checkChainInvariant state "flow-map-1" "{a: b}"
  checkChainInvariant state "flow-nested-mixed" "[{a: [b, {c: d}]}, e]"
  checkChainInvariant state "block-map-1" "a: b"
  checkChainInvariant state "block-map-2" "a: b\nc: d"
  checkChainInvariant state "block-seq-2" "- a\n- b"
  checkChainInvariant state "explicit-key" "? a\n: b"
  checkChainInvariant state "multi-doc" "---\na: b\n...\n---\nc: d"
  checkChainInvariant state "emit-nested"
    (emit (seqv [mapv [(sv "k", seqv [sv "a", sv "b"])]]))
  checkChainInvariant state "kitchen-sink"
    "%YAML 1.2\n---\nitems:\n  - name: \"alice\"\n    roles: [admin, user]\n  - name: 'bob'\n    tags:\n      ? key1\n      : val1\n...\n---\nsecond: doc"

/-! ## Priority 5 — ScannerBound theorems (BoundInv preservation)

Three sorry'd theorems in `ScannerBound.lean` claim that `BoundInv` is preserved
through scanner dispatch phases:

- `preprocess_preserves_bound`: `scanNextToken_preprocess` preserves BoundInv
  (involves `skipToContent` loop, `unwindIndents` loop, `saveSimpleKey`)
- `dispatchStructural_preserves_bound`: `scanNextToken_dispatchStructural` preserves BoundInv
  (involves `scanDocumentStart`/`scanDocumentEnd` with `advanceN 3`, `scanDirective` with loops)
- `dispatchContent_preserves_bound`: `scanNextToken_dispatchContent` preserves BoundInv
  (involves ALL scalar scanners, anchor/alias/tag scanners — all loop-based)

`BoundInv s₀ s` bundles four properties:
1. `s.offset ≤ s.inputEnd` (offset in bounds)
2. `s.inputEnd = s₀.inputEnd` (input end preserved)
3. `s.input = s₀.input` (input string preserved)
4. `String.Pos.Raw.IsValid s.input ⟨s.offset⟩` (offset at valid UTF-8 boundary)

We test by stepping through `scanNextToken` on diverse inputs, checking all four
properties at every step. Special emphasis on:
- Deep indent stacks (stresses `unwindIndents` loop)
- Multi-line scalars (stresses scalar scanner loops)
- UTF-8 multi-byte characters (stresses byte offset arithmetic)
-/

/-- Check whether a byte offset is at a valid UTF-8 character boundary in a string.
    Iterates through valid positions from the start. -/
def isAtCharBoundary (s : String) (offset : Nat) : Bool :=
  if offset == s.utf8ByteSize then true  -- one-past-end is valid
  else
    let rec go (byteIdx : Nat) (fuel : Nat) : Bool :=
      if fuel = 0 then false
      else if byteIdx == offset then true
      else if byteIdx ≥ s.utf8ByteSize then false
      else go (String.Pos.Raw.next s ⟨byteIdx⟩).byteIdx (fuel - 1)
    go 0 (s.utf8ByteSize + 1)

/-- Check BoundInv properties for one scanNextToken step.
    Returns `(offsetOk, inputEndOk, inputOk, isValidOk)`. -/
def checkBoundInv (s₀ s' : ScannerState) :
    Bool × Bool × Bool × Bool :=
  let offsetOk := s'.offset ≤ s'.inputEnd
  let inputEndOk := s'.inputEnd == s₀.inputEnd
  let inputOk := s'.input == s₀.input
  let isValidOk := isAtCharBoundary s'.input s'.offset
  (offsetOk, inputEndOk, inputOk, isValidOk)

/-- Drive scanning step-by-step, checking BoundInv at every step. -/
def checkBoundInvariant (state : IO.Ref TestCollector)
    (label : String) (input : String) : IO Unit := do
  let s0 := ScannerState.mk' input
  let s0 := s0.emit .streamStart
  let s0 := match s0.peek? with
    | some '\uFEFF' => s0.advance
    | _ => s0
  let fuel := (input.utf8ByteSize + 1) * 4
  let mut s := s0
  let mut step := 0
  let mut allOffsetOk := true
  let mut allInputEndOk := true
  let mut allInputOk := true
  let mut allIsValidOk := true
  let mut lastFailInfo := ""
  for _ in [:fuel] do
    match scanNextToken s with
    | .error _e =>
      -- Scan errors are fine for malformed inputs; just stop
      break
    | .ok none => break
    | .ok (some s') =>
      let (offsetOk, inputEndOk, inputOk, isValidOk) := checkBoundInv s0 s'
      if !offsetOk then
        allOffsetOk := false
        lastFailInfo := s!"offset fail at step {step}: offset={s'.offset}, inputEnd={s'.inputEnd}"
      if !inputEndOk then
        allInputEndOk := false
        lastFailInfo := s!"inputEnd fail at step {step}: s'.inputEnd={s'.inputEnd}, s₀.inputEnd={s0.inputEnd}"
      if !inputOk then
        allInputOk := false
        lastFailInfo := s!"input fail at step {step}: s'.input ≠ s₀.input"
      if !isValidOk then
        allIsValidOk := false
        lastFailInfo := s!"isValid fail at step {step}: offset={s'.offset} not at char boundary"
      s := s'
      step := step + 1
  checkM state s!"{label}: offset ≤ inputEnd ({step} steps)" allOffsetOk lastFailInfo
  checkM state s!"{label}: inputEnd preserved ({step} steps)" allInputEndOk lastFailInfo
  checkM state s!"{label}: input preserved ({step} steps)" allInputOk lastFailInfo
  checkM state s!"{label}: offset at char boundary ({step} steps)" allIsValidOk lastFailInfo

/-! ## Priority 5 Test Suites -/

def test5_bound (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "5: BoundInv preservation (preprocess/structural/content)"

  -- === preprocess_preserves_bound: skipToContent + unwindIndents ===

  -- Deep indent stacks (stress unwindIndents loop)
  checkBoundInvariant state "indent-2"
    "a:\n  b: c"
  checkBoundInvariant state "indent-3"
    "a:\n  b:\n    c: d"
  checkBoundInvariant state "indent-4"
    "a:\n  b:\n    c:\n      d: e"
  checkBoundInvariant state "indent-6"
    "a:\n  b:\n    c:\n      d:\n        e:\n          f: g"
  checkBoundInvariant state "indent-8"
    "a:\n  b:\n    c:\n      d:\n        e:\n          f:\n            g:\n              h: i"
  -- Deep then unwind (deep nesting followed by deindent triggers unwindIndents)
  checkBoundInvariant state "indent-unwind"
    "a:\n  b:\n    c: d\ne: f"
  checkBoundInvariant state "indent-unwind-deep"
    "a:\n  b:\n    c:\n      d: e\n  f: g\nh: i"
  -- Multiple sequence entries (repeated indent/unwind cycles)
  checkBoundInvariant state "seq-indent-cycle"
    "items:\n  - a\n  - b\n  - c\nother: x"

  -- Whitespace/comment skipping (skipToContent loop)
  checkBoundInvariant state "skip-spaces"
    "   a: b"
  checkBoundInvariant state "skip-tabs"
    "\t\ta: b"
  checkBoundInvariant state "skip-comment"
    "# comment\na: b"
  checkBoundInvariant state "skip-multi-comment"
    "# line1\n# line2\n# line3\na: b"
  checkBoundInvariant state "skip-blank-lines"
    "\n\n\na: b"
  checkBoundInvariant state "skip-mixed"
    "  # comment\n\n  # another\na: b"

  -- === dispatchStructural_preserves_bound: doc markers + directives ===

  -- Document start (advanceN 3)
  checkBoundInvariant state "doc-start"
    "---\na: b"
  -- Document end (advanceN 3)
  checkBoundInvariant state "doc-end"
    "a: b\n..."
  -- Multi-document (repeated doc start/end)
  checkBoundInvariant state "multi-doc"
    "---\na: b\n...\n---\nc: d\n..."
  -- YAML directive (loop-based)
  checkBoundInvariant state "yaml-directive"
    "%YAML 1.2\n---\na: b"
  -- TAG directive (loop-based)
  checkBoundInvariant state "tag-directive"
    "%TAG !t! tag:example.com,2000:\n---\na: b"
  -- Multiple directives
  checkBoundInvariant state "multi-directive"
    "%YAML 1.2\n%TAG !t! tag:example.com,2000:\n%TAG !u! tag:example.org,2026:\n---\na: b"

  -- === dispatchContent_preserves_bound: scalar/anchor/tag scanners ===

  -- Double-quoted scalars (loop-based)
  checkBoundInvariant state "dquoted-simple"
    "\"hello\""
  checkBoundInvariant state "dquoted-escape"
    "\"line1\\nline2\\ttab\""
  checkBoundInvariant state "dquoted-unicode-escape"
    "\"\\u0041\\u00E9\\U0001F600\""
  checkBoundInvariant state "dquoted-long"
    "\"abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ\""
  checkBoundInvariant state "dquoted-multiline"
    "\"line1\n  line2\n  line3\""
  checkBoundInvariant state "dquoted-empty"
    "\"\""

  -- Single-quoted scalars (loop-based)
  checkBoundInvariant state "squoted-simple"
    "'hello'"
  checkBoundInvariant state "squoted-escape"
    "'it''s escaped'"
  checkBoundInvariant state "squoted-long"
    "'abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'"
  checkBoundInvariant state "squoted-multiline"
    "'line1\n  line2\n  line3'"

  -- Block scalars (loop-based)
  checkBoundInvariant state "block-literal"
    "|\n  line1\n  line2\n  line3"
  checkBoundInvariant state "block-folded"
    ">\n  line1\n  line2\n  line3"
  checkBoundInvariant state "block-literal-long"
    "|\n  abcdefghijklmnopqrstuvwxyz\n  0123456789ABCDEF\n  final"
  checkBoundInvariant state "block-keep"
    "|+\n  line1\n  line2\n"
  checkBoundInvariant state "block-strip"
    "|-\n  line1\n  line2"
  checkBoundInvariant state "block-indent"
    "|2\n  line1\n  line2"

  -- Plain scalars (loop-based, implicit)
  checkBoundInvariant state "plain-simple"
    "hello"
  checkBoundInvariant state "plain-multiword"
    "hello world"
  checkBoundInvariant state "plain-long"
    "abcdefghijklmnopqrstuvwxyz0123456789"
  checkBoundInvariant state "plain-multiline"
    "line1\n  line2\n  line3"

  -- Anchor scanner (loop-based)
  checkBoundInvariant state "anchor-short"
    "&a value"
  checkBoundInvariant state "anchor-long"
    "&longanchorname value"
  checkBoundInvariant state "alias-short"
    "&a value\n*a"
  checkBoundInvariant state "alias-long"
    "&longanchorname value\n*longanchorname"

  -- Tag scanner (loop-based)
  checkBoundInvariant state "tag-named"
    "!!str hello"
  checkBoundInvariant state "tag-verbatim"
    "!<tag:yaml.org,2002:str> hello"
  checkBoundInvariant state "tag-custom"
    "!custom hello"

  -- === UTF-8 multi-byte characters (byte offset arithmetic) ===

  checkBoundInvariant state "utf8-2byte"
    "key: résumé"
  checkBoundInvariant state "utf8-3byte"
    "key: 日本語"
  checkBoundInvariant state "utf8-4byte"
    "key: 𝕊𝕖𝕥"
  checkBoundInvariant state "utf8-mixed"
    "名前: résumé\n値: 𝕊𝕖𝕥"
  checkBoundInvariant state "utf8-dquoted"
    "\"résumé café naïve\""
  checkBoundInvariant state "utf8-squoted"
    "'日本語テスト'"
  checkBoundInvariant state "utf8-plain"
    "日本語テスト"
  checkBoundInvariant state "utf8-anchor"
    "&名前 日本語"
  checkBoundInvariant state "utf8-tag"
    "!!str 日本語"
  checkBoundInvariant state "utf8-block-literal"
    "|\n  日本語\n  中文\n  한국어"
  checkBoundInvariant state "utf8-deep"
    "名前:\n  性: 田中\n  名:\n    漢字: 太郎\n    読み: たろう"
  -- Emoji (4-byte UTF-8)
  checkBoundInvariant state "utf8-emoji"
    "mood: \"😀😎🎉\""
  -- Mixed ASCII and multi-byte in flow
  checkBoundInvariant state "utf8-flow"
    "[résumé, 日本語, 𝕊𝕖𝕥]"
  checkBoundInvariant state "utf8-flow-map"
    "{名前: 太郎, 年齢: \"25\"}"

  -- === Combined / stress tests ===

  -- All dispatch phases in one input
  checkBoundInvariant state "all-phases"
    "%YAML 1.2\n---\nitems:\n  - \"quoted\"\n  - 'single'\n  - &anc plain\n  - *anc\n  - !!str tagged\n  - |\n    block\n...\n---\nsecond: doc"

  -- Deep nesting with flow (unwind + flow dispatch)
  checkBoundInvariant state "deep-flow-nested"
    "a:\n  b:\n    c: [{d: [e, f]}, {g: [h]}]"

  -- Wide block sequence with mixed content
  checkBoundInvariant state "wide-mixed-content"
    "- \"q1\"\n- 'q2'\n- plain\n- &a val\n- *a\n- !!int 42\n- |\n  block\n- >\n  folded"

  -- Emitter output (exercises the exact patterns theorems care about)
  checkBoundInvariant state "emit-seq"
    (emit (seqv [sv "a", sv "b", sv "c"]))
  checkBoundInvariant state "emit-map"
    (emit (mapv [(sv "k", sv "v"), (sv "k2", sv "v2")]))
  checkBoundInvariant state "emit-nested"
    (emit (seqv [mapv [(sv "k", seqv [sv "a", sv "b"])]]))
  checkBoundInvariant state "emit-deep"
    (emit (seqv [seqv [seqv [seqv [sv "a"]]]]))
  checkBoundInvariant state "emit-complex"
    (emit (mapv [(sv "users",
                  seqv [mapv [(sv "name", sv "alice"),
                              (sv "roles", seqv [sv "admin", sv "user"])],
                        mapv [(sv "name", sv "bob"),
                              (sv "roles", seqv [sv "user"])]]),
                 (sv "version", sv "2.0")]))

  -- UTF-8 emitter output
  checkBoundInvariant state "emit-utf8"
    (emit (mapv [(sv "名前", sv "太郎"), (sv "値", sv "résumé")]))

  -- Edge cases
  checkBoundInvariant state "empty"
    ""
  checkBoundInvariant state "whitespace-only"
    "   "
  checkBoundInvariant state "newlines-only"
    "\n\n\n"
  checkBoundInvariant state "bom"
    "\uFEFF---\na: b"

/-! ## Priority 6 — ScanChain_filtered_prefix

`ScanChain_filtered_prefix` (EmitterScannability.lean) claims: given
`FlowMonoChain fl₀ s n s'`, `s.simpleKey.possible = false`,
`s.simpleKeyStack.size ≥ s.flowLevel`, and a stack-floor condition,
then `∃ suffix, (s'.tokens.filter notPlaceholder) = (s.tokens.filter notPlaceholder) ++ suffix`.

The precondition was strengthened on 2026-04-15 (commit 92c7903d) from a
disjunction allowing `explicitKeyLine = none` to the current `simpleKey.possible = false`:
the older disjunction was empirically unsound because `saveSimpleKey` reserves a
placeholder that `scanValue` later overwrites, inserting into the interior of the
filtered array. The probe below exercises the current precondition across all
intermediate scan states.

For every pair of states `s_i, s_j` (i < j) where `s_i.simpleKey.possible = false`,
we verify that `(s_j.tokens.filter notPlaceholder)` begins with
`(s_i.tokens.filter notPlaceholder)`.
-/

/-- Check filtered prefix preservation at every intermediate state where the
    current theorem's `simpleKey.possible = false` precondition holds. -/
def checkFilteredPrefix (state : IO.Ref TestCollector)
    (label : String) (input : String) : IO Unit := do
  let s0 := ScannerState.mk' input
  let s0 := s0.emit .streamStart
  let s0 := match s0.peek? with
    | some '\uFEFF' => s0.advance
    | _ => s0
  let fuel := (input.utf8ByteSize + 1) * 4
  -- Collect all intermediate states
  let mut states : Array ScannerState := #[s0]
  let mut s := s0
  for _ in [:fuel] do
    match scanNextToken s with
    | .error _ => break
    | .ok none => break
    | .ok (some s') =>
      states := states.push s'
      s := s'
  let p : Positioned YamlToken → Bool := fun t => t.val != .placeholder
  -- For every pair (i, j) where i < j and `sk.possible = false` at state i,
  -- check that filtered(state_j) has filtered(state_i) as a prefix.
  let mut allSkOk := true
  let mut skFails := 0
  let mut skPairs := 0
  let mut lastFailInfo := ""
  for i in [:states.size] do
    let si := states[i]!
    if si.simpleKey.possible then continue
    let filt_i := si.tokens.filter p
    for j in [i+1:states.size] do
      let sj := states[j]!
      let filt_j := sj.tokens.filter p
      let prefixOk :=
        if filt_i.size > filt_j.size then false
        else (List.range filt_i.size).all fun k =>
          if h₁ : k < filt_i.size then
            if h₂ : k < filt_j.size then
              filt_j[k] == filt_i[k]
            else false
          else true
      skPairs := skPairs + 1
      if !prefixOk then
        allSkOk := false
        skFails := skFails + 1
        lastFailInfo := s!"filtered prefix FAIL (sk.possible=false): step {i}→{j}, " ++
          s!"filt_i.size={filt_i.size}, filt_j.size={filt_j.size}, " ++
          s!"si.tokens.size={si.tokens.size}, sj.tokens.size={sj.tokens.size}, " ++
          s!"si.ek={si.explicitKeyLine.isSome}"
  checkM state s!"{label}: filtered prefix (sk.possible=false, {skPairs} pairs)" allSkOk
    (if skFails > 0 then s!"{skFails} failures. Last: {lastFailInfo}" else "")

  -- Also check: at call sites, does ek=none actually hold after flow open?
  -- Track when ek becomes none and whether it stays none during flow body
  -- Sanity check that the call-site precondition is actually reachable:
  -- after every flow open, `sk.possible = false` should hold (this is the
  -- property `scanNextToken_flow_open_init` establishes for the two call sites).
  let mut flowOpens := 0
  let mut skFalseAtFlowOpen := 0
  for i in [:states.size] do
    let si := states[i]!
    if i > 0 then
      let prev := states[i-1]!
      if si.tokens.size > prev.tokens.size then
        let lastAdded := si.tokens[si.tokens.size - 1]!.val
        if lastAdded == .flowSequenceStart || lastAdded == .flowMappingStart then
          flowOpens := flowOpens + 1
          if !si.simpleKey.possible then
            skFalseAtFlowOpen := skFalseAtFlowOpen + 1
  check state s!"{label}: sk.possible=false at flow opens ({skFalseAtFlowOpen}/{flowOpens})"
    (flowOpens == 0 || skFalseAtFlowOpen == flowOpens)

/-- Detailed diagnostic for a single input: dump all intermediate states'
    filtered tokens, ek, sk state, and identify exact token changes. -/
def diagFilteredPrefix (state : IO.Ref TestCollector)
    (label : String) (input : String) : IO Unit := do
  let s0 := ScannerState.mk' input
  let s0 := s0.emit .streamStart
  let s0 := match s0.peek? with
    | some '\uFEFF' => s0.advance
    | _ => s0
  let fuel := (input.utf8ByteSize + 1) * 4
  let mut states : Array ScannerState := #[s0]
  let mut s := s0
  for _ in [:fuel] do
    match scanNextToken s with
    | .error _ => break
    | .ok none => break
    | .ok (some s') =>
      states := states.push s'
      s := s'
  let p : Positioned YamlToken → Bool := fun t => t.val != .placeholder
  -- Dump each step's filtered tokens, raw tokens, sk, ek
  for i in [:states.size] do
    let si := states[i]!
    let filt := si.tokens.filter p
    let filtVals := filt.toList.map (fun t => tokStr t.val)
    let rawVals := si.tokens.toList.map (fun t => tokStr t.val)
    IO.println s!"  step {i}: ek={si.explicitKeyLine.isSome} sk.pos={si.simpleKey.possible} sk.idx={si.simpleKey.tokenIndex} raw={rawVals} filt={filtVals}"
  -- Check for prefix violations under the current `sk.possible = false` precondition
  for i in [:states.size] do
    let si := states[i]!
    if si.simpleKey.possible then continue
    let filt_i := si.tokens.filter p
    for j in [i+1:states.size] do
      let sj := states[j]!
      let filt_j := sj.tokens.filter p
      for k in [:filt_i.size] do
        if h₁ : k < filt_i.size then
          if h₂ : k < filt_j.size then
            if !(filt_j[k] == filt_i[k]) then
              IO.println s!"  MISMATCH step {i}→{j} pos {k}: was {tokStr filt_i[k].val} now {tokStr filt_j[k].val}"
  check state s!"{label}: diagnostic complete" true

def test_filtered_prefix (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "ScanChain_filtered_prefix"

  -- Diagnostic on smallest failing case
  IO.println "=== Diagnostic: simple-key-val ==="
  diagFilteredPrefix state "diag-simple-key-val" "a: b"
  IO.println "=== Diagnostic: emit-map-1 ==="
  diagFilteredPrefix state "diag-emit-map-1" (emit (mapv [(sv "k", sv "v")]))

  -- === Emitter-produced inputs (the actual use case) ===
  checkFilteredPrefix state "emit-seq-1"
    (emit (seqv [sv "a"]))
  checkFilteredPrefix state "emit-seq-3"
    (emit (seqv [sv "a", sv "b", sv "c"]))
  checkFilteredPrefix state "emit-map-1"
    (emit (mapv [(sv "k", sv "v")]))
  checkFilteredPrefix state "emit-map-2"
    (emit (mapv [(sv "k", sv "v"), (sv "k2", sv "v2")]))
  checkFilteredPrefix state "emit-nested-seq"
    (emit (seqv [seqv [sv "a", sv "b"], sv "c"]))
  checkFilteredPrefix state "emit-nested-map"
    (emit (seqv [mapv [(sv "k", sv "v")], sv "c"]))
  checkFilteredPrefix state "emit-deep"
    (emit (seqv [seqv [seqv [sv "a"]]]))
  checkFilteredPrefix state "emit-mixed"
    (emit (mapv [(sv "k", seqv [sv "a", sv "b"]),
                 (sv "k2", mapv [(sv "a", sv "b")])]))
  checkFilteredPrefix state "emit-complex"
    (emit (mapv [(sv "users",
                  seqv [mapv [(sv "name", sv "alice"),
                              (sv "roles", seqv [sv "admin", sv "user"])],
                        mapv [(sv "name", sv "bob"),
                              (sv "roles", seqv [sv "user"])]]),
                 (sv "version", sv "2.0")]))

  -- === Adversarial non-emitter inputs ===
  -- These exercise scanner states that emitter output never produces,
  -- probing for filtered prefix violations.

  -- Simple key with value (scanValuePrepare overwrites placeholder → .key)
  checkFilteredPrefix state "simple-key-val" "a: b"
  checkFilteredPrefix state "simple-key-nested" "a: b\nc: d"
  checkFilteredPrefix state "explicit-key" "? a\n: b"

  -- Flow collections (exercises flow stack save/restore)
  checkFilteredPrefix state "flow-seq" "[a, b, c]"
  checkFilteredPrefix state "flow-map" "{a: b, c: d}"
  checkFilteredPrefix state "flow-nested" "[[a, b], [c, d]]"
  checkFilteredPrefix state "flow-deep" "[{a: [b, {c: d}]}, e]"

  -- Block indicators (keys + values + entries)
  checkFilteredPrefix state "block-seq" "- a\n- b\n- c"
  checkFilteredPrefix state "block-map" "a: b\nc: d\ne: f"
  checkFilteredPrefix state "block-mixed" "items:\n  - a\n  - b"
  checkFilteredPrefix state "block-nested" "a:\n  b:\n    c: d"

  -- Quoted scalars
  checkFilteredPrefix state "dquoted" "\"hello world\""
  checkFilteredPrefix state "squoted" "'hello world'"
  checkFilteredPrefix state "flow-dquoted" "[\"a\", \"b\"]"

  -- Document markers
  checkFilteredPrefix state "doc-start" "---\na: b"
  checkFilteredPrefix state "doc-end" "a: b\n..."
  checkFilteredPrefix state "multi-doc" "---\na: b\n...\n---\nc: d"

  -- Directives (only YAML/TAG — no %RESERVED since scanner errors differ)
  checkFilteredPrefix state "yaml-directive" "%YAML 1.2\n---\na: b"
  checkFilteredPrefix state "tag-directive" "%TAG !t! tag:\n---\na: b"

  -- Edge cases: empty, whitespace
  checkFilteredPrefix state "empty" ""
  checkFilteredPrefix state "ws-only" "   "
  checkFilteredPrefix state "plain-scalar" "hello"

  -- Stress: deeply nested flow within block
  checkFilteredPrefix state "deep-flow-in-block"
    "a:\n  b:\n    c: [{d: [e, {f: [g]}]}, h]"

/-! ## Priority 6 — Flow parser helper lemmas (parseNode nested brackets)

These 3 helper lemmas support `flow_parser_ok_of_structure` and handle nested
bracket cases within flow sequences and mappings:

1. `parseNode_flowSeqStart_in_seq` — parseNode on nested `[...]` inside a sequence
2. `parseNode_flowMapStart_in_seq` — parseNode on nested `{...}` inside a sequence
3. `parseEntry_in_flowMap` — parseExplicitKey + parseFlowMappingValue in a mapping

These have HIGH statement risk (∀ over parse states, complex bracket balance conditions)
and HIGH proof cost (require coordination with loop theorems). Adversarial instantiation
is critical before investing proof effort.

We test the key claims:
- parseNode/parseExplicitKey succeed with sufficient fuel
- Result position advances and stays within bounds
- Result peek is flowEntry or appropriate terminator
- Bracket balance is maintained
-/

/-- Find the first content-start position in a flow sequence body (after `[`). -/
private def findContentInSeq (tokens : Array (Positioned YamlToken)) (bodyStart : Nat) : Option Nat := do
  for _h : i in [bodyStart:tokens.size] do
    let tok := tokens[i]!.val
    if isContentStart tok then
      return i
  none

/-- Find the first .key position in a flow mapping body (after `{`). -/
def findKeyInMap (tokens : Array (Positioned YamlToken)) (bodyStart : Nat) : Option Nat := do
  for _h : i in [bodyStart:tokens.size] do
    let tok := tokens[i]!.val
    if tok == .key then
      return i
  none

/-- Check parseNode on nested flowSeqStart inside a sequence body. -/
def checkNestedSeqInSeq (state : IO.Ref TestCollector)
    (label : String) (outerSeq : List YamlValue) : IO Unit := do
  let emitted := emit (seqv outerSeq)
  match scanFiltered emitted with
  | .error e =>
    checkM state s!"{label}: scan ok" false s!"scan error: {repr e}"
  | .ok tokens =>
    check state s!"{label}: scan ok" true

    -- Find the outer `[` at position 1 (after streamStart)
    if tokens.size < 3 then
      checkM state s!"{label}: has tokens" false s!"only {tokens.size} tokens"
      return

    check state s!"{label}: outer [" (tokens[1]!.val == .flowSequenceStart)

    let bodyStart := 2
    -- Find first nested `[` in the body
    let mut foundNested := false
    for _h : i in [bodyStart:tokens.size] do
      let tok := tokens[i]!.val
      if tok == .flowSequenceStart then
        let bal := bracketBal tokens bodyStart i
        if bal == 0 then
          foundNested := true
          -- Try to parse at this position
          let ps : ParseState := { tokens := tokens, pos := i }
          let fuel := 4 * tokens.size + 4
          match parseNode ps fuel with
          | .ok (_, ps') =>
            check state s!"{label}: parseNode@{i} ok" true
            check state s!"{label}: parseNode@{i} advances" (ps'.pos > i)
            check state s!"{label}: parseNode@{i} tokens preserved" (ps'.tokens.size == tokens.size)
          | .error e =>
            checkM state s!"{label}: parseNode@{i} ok" false s!"parse error: {repr e}"
          break

    check state s!"{label}: found nested [" foundNested

/-- Check parseNode on nested flowMapStart inside a sequence body. -/
def checkNestedMapInSeq (state : IO.Ref TestCollector)
    (label : String) (outerSeq : List YamlValue) : IO Unit := do
  let emitted := emit (seqv outerSeq)
  match scanFiltered emitted with
  | .error e =>
    checkM state s!"{label}: scan ok" false s!"scan error: {repr e}"
  | .ok tokens =>
    check state s!"{label}: scan ok" true

    if tokens.size < 3 then
      checkM state s!"{label}: has tokens" false s!"only {tokens.size} tokens"
      return

    check state s!"{label}: outer [" (tokens[1]!.val == .flowSequenceStart)

    let bodyStart := 2
    -- Find first nested `{` in the body
    let mut foundNested := false
    for _h : i in [bodyStart:tokens.size] do
      let tok := tokens[i]!.val
      if tok == .flowMappingStart then
        let bal := bracketBal tokens bodyStart i
        if bal == 0 then
          foundNested := true
          -- Try to parse at this position
          let ps : ParseState := { tokens := tokens, pos := i }
          let fuel := 4 * tokens.size + 4
          match parseNode ps fuel with
          | .ok (_, ps') =>
            check state s!"{label}: parseNode@{i} ok" true
            check state s!"{label}: parseNode@{i} advances" (ps'.pos > i)
            check state s!"{label}: parseNode@{i} tokens preserved" (ps'.tokens.size == tokens.size)
          | .error e =>
            checkM state s!"{label}: parseNode@{i} ok" false s!"parse error: {repr e}"
          break

    check state s!"{label}: found nested \{" foundNested

/-- Check parseExplicitKey + parseFlowMappingValue on a map entry. -/
def checkMapEntry (state : IO.Ref TestCollector)
    (label : String) (outerMap : List (YamlValue × YamlValue)) : IO Unit := do
  let emitted := emit (mapv outerMap)
  match scanFiltered emitted with
  | .error e =>
    checkM state s!"{label}: scan ok" false s!"scan error: {repr e}"
  | .ok tokens =>
    check state s!"{label}: scan ok" true

    if tokens.size < 3 then
      checkM state s!"{label}: has tokens" false s!"only {tokens.size} tokens"
      return

    check state s!"{label}: outer \{" (tokens[1]!.val == .flowMappingStart)

    let bodyStart := 2
    -- Find first .key in the body
    match findKeyInMap tokens bodyStart with
    | none =>
      checkM state s!"{label}: found .key" false "no .key found"
    | some keyPos =>
      check state s!"{label}: found .key@{keyPos}" true

      -- Try parseExplicitKey at keyPos
      let ps : ParseState := { tokens := tokens, pos := keyPos }
      let fuel := 4 * tokens.size + 4
      match parseExplicitKey ps.advance fuel with
      | .ok (_, keyPs) =>
        check state s!"{label}: parseExplicitKey ok" true
        check state s!"{label}: parseExplicitKey advances" (keyPs.pos > keyPos)

        -- Try parseFlowMappingValue at the result position
        match parseFlowMappingValue keyPs fuel #[] "testkey" with
        | .ok (_, valPs) =>
          check state s!"{label}: parseFlowMappingValue ok" true
          check state s!"{label}: parseFlowMappingValue advances" (valPs.pos > keyPs.pos)
          check state s!"{label}: tokens preserved" (valPs.tokens.size == tokens.size)
        | .error e =>
          checkM state s!"{label}: parseFlowMappingValue ok" false s!"parse error: {repr e}"
      | .error e =>
        checkM state s!"{label}: parseExplicitKey ok" false s!"parse error: {repr e}"

/-! ## Priority 6 Test Suites -/

def testFlowParserHelpers (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 6: Flow parser helper lemmas"

  -- parseNode_flowSeqStart_in_seq tests
  checkNestedSeqInSeq state "nested-seq-1" [seqv [sv "a"]]
  checkNestedSeqInSeq state "nested-seq-2" [seqv [sv "a", sv "b"]]
  checkNestedSeqInSeq state "nested-seq-deep" [seqv [seqv [sv "a"]]]
  checkNestedSeqInSeq state "nested-seq-after-scalar" [sv "x", seqv [sv "a"]]
  checkNestedSeqInSeq state "nested-seq-multi" [seqv [sv "1", sv "2"], seqv [sv "3"]]

  -- parseNode_flowMapStart_in_seq tests
  checkNestedMapInSeq state "nested-map-1" [mapv [(sv "k", sv "v")]]
  checkNestedMapInSeq state "nested-map-2" [mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")]]
  checkNestedMapInSeq state "nested-map-deep" [mapv [(sv "k", mapv [(sv "inner", sv "v")])]]
  checkNestedMapInSeq state "nested-map-after-scalar" [sv "x", mapv [(sv "k", sv "v")]]
  checkNestedMapInSeq state "nested-map-mixed" [mapv [(sv "k", seqv [sv "a"])]]

  -- parseEntry_in_flowMap tests
  checkMapEntry state "map-entry-1" [(sv "k", sv "v")]
  checkMapEntry state "map-entry-2" [(sv "k1", sv "v1"), (sv "k2", sv "v2")]
  checkMapEntry state "map-entry-nested-val-seq" [(sv "k", seqv [sv "a", sv "b"])]
  checkMapEntry state "map-entry-nested-val-map" [(sv "k", mapv [(sv "inner", sv "v")])]
  checkMapEntry state "map-entry-complex" [(sv "k1", seqv [sv "a"]), (sv "k2", mapv [(sv "x", sv "y")])]
  checkMapEntry state "map-entry-deep" [(sv "k", seqv [mapv [(sv "inner", seqv [sv "deep"])]])]

/-! ## Priority 7 — `handleBlockMappingKeyEntry_mono_step`

Fuel monotonicity for `handleBlockMappingKeyEntry`: if the helper succeeds
at fuel `n+1`, it succeeds at `n+2` with the **same result** (same key,
value, and resulting parser state).

**Risk:** MEDIUM. The theorem's universal quantification over `n : Nat`,
`ps : ParseState`, and `idx : Nat` is standard fuel-monotonicity shape
(typically true). The theorem does depend on a `parseNode` monotonicity
hypothesis (`ih_pn`) and a `parseBlockMappingEntryValue` monotonicity
helper (`h_bmv`), so if those were false, this would inherit that.

**Audit approach:** Exercise `handleBlockMappingKeyEntry` over block-style
YAML inputs (scalar keys, complex keys, nested values, empty values), at
several fuel values spanning the success threshold, and check that the
result is preserved across `(n+1) → (n+2)`.
-/

/-- Find the first `.key` token position in `tokens`. -/
def findKeyPos (tokens : Array (Positioned YamlToken)) : Option Nat := do
  for _h : i in [0:tokens.size] do
    if tokens[i]!.val == .key then
      return i
  none

/-- Compare two `(YamlValue × YamlValue × ParseState)` results structurally
    (key, val, pos, tokens.size). ParseState has no derived `BEq`, so we
    compare observable fields. -/
def resultEq
    (r1 r2 : YamlValue × YamlValue × ParseState) : Bool :=
  r1.fst == r2.fst && r1.snd.fst == r2.snd.fst &&
  r1.snd.snd.pos == r2.snd.snd.pos &&
  r1.snd.snd.tokens.size == r2.snd.snd.tokens.size

/-- Check parseNode monotonicity at fuel `n` for a given `ps`: equivalent
    of the `ih_pn` hypothesis in the theorem. Returns `true` if the
    monotonicity property holds for this specific `(ps, n)`. Used to
    distinguish true theorem violations from cases where the `ih_pn`
    hypothesis itself is false (vacuously satisfying the implication). -/
def parseNodeMonoHoldsAt (ps : ParseState) (n : Nat) : Bool :=
  match parseNode ps (n + 1), parseNode ps (n + 2) with
  | .ok v1, .ok v2 => v1.fst == v2.fst && v1.snd.pos == v2.snd.pos
  | .ok _, .error _ => false  -- lost success = not monotonic
  | .error _, _ => true       -- (n+1) failed → ih_pn vacuous

/-- Check parseBlockMappingEntryValue monotonicity at fuel `n` for a given
    `ps, khc, kl, kc`: equivalent of the `h_bmv` hypothesis.  -/
def parseBMVMonoHoldsAt (ps : ParseState) (khc : Bool) (kl kc : Nat)
    (n : Nat) : Bool :=
  match parseBlockMappingEntryValue ps (n + 1) khc kl kc,
        parseBlockMappingEntryValue ps (n + 2) khc kl kc with
  | .ok v1, .ok v2 => v1.fst == v2.fst && v1.snd.pos == v2.snd.pos
  | .ok _, .error _ => false
  | .error _, _ => true

/-- For a given `input`, find the first `.key` position and for fuel values
    spanning the success threshold, verify that success at `n+1` implies
    success at `n+2` with the **same result**. Skip checks where `ih_pn`
    at fuel `n` (evaluated on `ps.advance`) doesn't hold, as the theorem
    is vacuous there. -/
def checkBMKEMono (state : IO.Ref TestCollector)
    (label : String) (input : String) : IO Unit := do
  match scanFiltered input with
  | .error e =>
    checkM state s!"{label}: scan ok" false s!"scan error: {repr e}"
  | .ok tokens =>
    check state s!"{label}: scan ok" true
    match findKeyPos tokens with
    | none =>
      checkM state s!"{label}: has .key" false "no .key token in scan output"
    | some keyPos =>
      check state s!"{label}: found .key@{keyPos}" true
      let ps : ParseState := { tokens := tokens, pos := keyPos }
      let psAdv := ps.advance
      -- Sweep fuel from 1 to 4*size+8 to exercise both the
      -- insufficient-fuel and sufficient-fuel regimes.
      let fuelMax := 4 * tokens.size + 8
      let mut regressionSeen := false
      let mut vacuousCount := 0
      let mut firstSuccess : Option Nat := none
      for _h : fuel in [1:fuelMax] do
        -- Only check cases where BOTH hypotheses hold: ih_pn (parseNode
        -- mono at fuel `fuel` on ps.advance) AND h_bmv (parseBMV mono at
        -- fuel `fuel`). If either fails, the theorem's hypothesis is
        -- false, making the implication vacuously true.
        let ihPnOk := parseNodeMonoHoldsAt psAdv fuel
        -- h_bmv is universally quantified in the theorem, so we need it
        -- to hold for any (ps', khc, kl, kc) that might be passed in.
        -- Pragmatic approximation: check h_bmv on the canonical ps after
        -- parseNode would succeed, and a boolean khc derived from peek.
        let psForBmv :=
          match parseNode psAdv (fuel + 1) with
          | .ok (_, psPost) => psPost
          | .error _ => psAdv
        let khc : Bool :=
          match psAdv.peek? with
          | some YamlToken.value | some YamlToken.blockEnd => false
          | _ => true
        let hBmvOk := parseBMVMonoHoldsAt psForBmv khc 0 0 fuel
        if !ihPnOk || !hBmvOk then
          vacuousCount := vacuousCount + 1
        else
          let r1 := handleBlockMappingKeyEntry ps (fuel + 1) 0
          let r2 := handleBlockMappingKeyEntry ps (fuel + 2) 0
          match r1, r2 with
          | .ok v1, .ok v2 =>
            if firstSuccess.isNone then firstSuccess := some (fuel + 1)
            let eq := resultEq v1 v2
            check state s!"{label}: mono@fuel{fuel+1}→{fuel+2} result preserved" eq
            if !eq then regressionSeen := true
          | .ok _, .error _ =>
            -- CRITICAL: counterexample to the theorem (both hypotheses hold).
            checkM state s!"{label}: mono@fuel{fuel+1}→{fuel+2} NO REGRESSION"
              false "more fuel produced .error despite ih_pn + h_bmv (theorem violated)"
            regressionSeen := true
          | .error _, _ =>
            -- (n+1) didn't succeed; nothing to verify.
            pure ()
      check state s!"{label}: some fuel succeeded" firstSuccess.isSome
      check state s!"{label}: no regression where ih_pn+h_bmv hold" (!regressionSeen)
      if let some f := firstSuccess then
        check state s!"{label}: first success (ih_pn-guarded) fuel = {f}" true
      if vacuousCount > 0 then
        check state s!"{label}: vacuous-ih_pn fuel count = {vacuousCount}" true

/-- Priority 7 test suite: `handleBlockMappingKeyEntry` mono step. -/
def testHandleBlockMappingKeyEntryMono (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 7: handleBlockMappingKeyEntry_mono_step"

  -- Simple implicit keys (scalar: scalar)
  checkBMKEMono state "implicit-simple" "a: b"
  checkBMKEMono state "implicit-two-pairs" "a: b\nc: d"
  checkBMKEMono state "implicit-three-pairs" "a: 1\nb: 2\nc: 3"

  -- Empty key (explicit `?` with no content)
  checkBMKEMono state "explicit-empty-key" "?\n: v"
  checkBMKEMono state "explicit-key-only" "? key"

  -- Explicit key with content
  checkBMKEMono state "explicit-full" "? k\n: v"
  checkBMKEMono state "explicit-two" "? k1\n: v1\n? k2\n: v2"

  -- Block nested value: sequence
  checkBMKEMono state "block-value-seq" "k:\n  - a\n  - b"
  checkBMKEMono state "block-value-seq-nested" "k:\n  - a\n  - - b\n    - c"

  -- Block nested value: mapping
  checkBMKEMono state "block-value-map" "k:\n  a: 1\n  b: 2"
  checkBMKEMono state "block-value-map-deep" "k:\n  a:\n    b: c"

  -- Flow value inside block mapping
  checkBMKEMono state "flow-value-seq" "k: [a, b, c]"
  checkBMKEMono state "flow-value-map" "k: {a: 1, b: 2}"
  checkBMKEMono state "flow-value-complex" "k: [{a: 1}, [b, c]]"

  -- Quoted scalars
  checkBMKEMono state "quoted-value" "k: \"hello\""
  checkBMKEMono state "quoted-key" "\"k\": v"

  -- Null and boolean-ish
  checkBMKEMono state "null-value" "k: ~"
  checkBMKEMono state "empty-value" "k:"

  -- Complex nested structures
  checkBMKEMono state "complex-1" "a:\n  b:\n    - c\n    - d\ne: f"
  checkBMKEMono state "complex-2" "root:\n  list:\n    - item1\n    - item2\n  map:\n    key: value"

/-! ## Priority 8 — `closeStaleExplicitKey_cases` and the stale-register projections (item 333)

`closeStaleExplicitKey` (legacy) and `closeStaleExplicitKeyIx` (indexed) end a
pending explicit key whose entry a sibling has closed.  The lemma family in
`L4YAML/Proofs/Scanner/CloseStaleExplicitKey{,Ix}.lean` claims (i) the hook is
the identity or EXACTLY the reset of `explicitKeyLine`/`explicitKeyCol`
(`_cases`), (ii) every other projection passes through (`_tokens`, `_offset`,
`_flowLevel`, `_simpleKey`, …), (iii) the identity holds in flow and on a dead
register (`_of_inFlow`, `_of_ek_none`).

**Risk:** LOW on (i)/(iii) — they are by `split`.  MEDIUM on (ii) and on
which arm fires: the arm is the behaviour item 333 measured (`? a⏎[1]: b`
re-reads as `{a: null, [1]: b}`), and the exceptions `:`/`-`/`?` are what keep
`?⏎- a⏎- b⏎: v` a sequence key.  A wrong exception set would compile and pass
the lemmas (they hold for ANY exception set) — only an instantiation sees it.

**Audit approach:** build states parked at a line start with the register set
by hand (live/dead, block/flow, sibling at/left of/right of the `?` column,
each exception character, same line, end of input), run both hooks, and check
(a) the result is one of the two arms with ALL other projections equal,
(b) the arm is the one the input owes, (c) legacy and indexed agree.
-/

open L4YAML.Scanner.Indexed

/-- A legacy state parked at `(offset, line, col)` of `input` with the explicit-key
    register and flow depth set by hand. -/
def staleStateAt (input : String) (offset line col : Nat) (ek : Option Nat) (ekc : Int)
    (flowLevel : Nat) : ScannerState :=
  let s0 : ScannerState := ScannerState.mk' input
  { s0 with offset := offset, line := line, col := col,
            explicitKeyLine := ek, explicitKeyCol := ekc, flowLevel := flowLevel }

/-- The indexed twin of `staleStateAt` (ASCII inputs: `offset` characters = bytes). -/
def staleStateIxAt (input : String) (offset : Nat) (ek : Option Nat) (ekc : Int)
    (flowLevel : Nat) : ScannerStateIx input :=
  let t0 : ScannerStateIx input := (ScannerStateIx.mk' input).advanceN offset
  { t0 with explicitKeyLine := ek, explicitKeyCol := ekc, flowLevel := flowLevel }

/-- Every projection of a legacy state EXCEPT the register, as one comparable tuple. -/
def nonRegisterView (s : ScannerState) :
    Nat × Nat × Nat × Nat × Nat × Nat × Bool × Nat × Bool :=
  (s.offset, s.line, s.col, s.tokens.size, s.indents.size, s.flowLevel,
   s.simpleKeyAllowed, s.explicitKeyStack.size, s.needIndentCheck)

def nonRegisterViewIx {input : String} (s : ScannerStateIx input) :
    Nat × Nat × Nat × Nat × Nat × Nat × Bool × Nat × Bool :=
  (s.cursor.pos.offset, s.cursor.pos.line, s.cursor.pos.col, s.tokens.size, s.indents.size,
   s.flowLevel, s.simpleKeyAllowed, s.explicitKeyStack.size, s.needIndentCheck)

/-- Which arm of `closeStaleExplicitKey_cases` a result took: `some true` = reset,
    `some false` = identity, `none` = neither (the dichotomy is violated). -/
def staleArm (before after : Option Nat × Int) : Option Bool :=
  if after == before then some false
  else if after == (none, -1) then some true
  else none

/-- One scenario: `input`, the cursor at the start of line `line` (byte `offset`, column `col`),
    the register `(ek, ekc)`, flow depth, and the arm the input owes (`true` = reset). -/
def checkStaleCase (state : IO.Ref TestCollector) (label input : String)
    (offset line col : Nat) (ek : Option Nat) (ekc : Int) (flowLevel : Nat)
    (expectReset : Bool) : IO Unit := do
  let s := staleStateAt input offset line col ek ekc flowLevel
  let s' := closeStaleExplicitKey s
  let armL := staleArm (s.explicitKeyLine, s.explicitKeyCol) (s'.explicitKeyLine, s'.explicitKeyCol)
  checkM state s!"{label}: legacy result is one of the two arms" armL.isSome
    s!"register went to ({repr s'.explicitKeyLine}, {s'.explicitKeyCol})"
  checkM state s!"{label}: legacy other projections pass through"
    (nonRegisterView s' == nonRegisterView s) s!"{repr (nonRegisterView s')} ≠ {repr (nonRegisterView s)}"
  checkM state s!"{label}: legacy arm is {if expectReset then "reset" else "identity"}"
    (armL == some expectReset) s!"got {repr armL}"
  let t := staleStateIxAt input offset ek ekc flowLevel
  checkM state s!"{label}: indexed cursor parked at the same place"
    (t.cursor.pos.line == line && t.cursor.pos.col == col) s!"cursor at {t.cursor.pos.line}:{t.cursor.pos.col}"
  let t' := t.closeStaleExplicitKeyIx
  let armI := staleArm (t.explicitKeyLine, t.explicitKeyCol) (t'.explicitKeyLine, t'.explicitKeyCol)
  checkM state s!"{label}: indexed result is one of the two arms" armI.isSome
    s!"register went to ({repr t'.explicitKeyLine}, {t'.explicitKeyCol})"
  checkM state s!"{label}: indexed other projections pass through"
    (nonRegisterViewIx t' == nonRegisterViewIx t) s!"{repr (nonRegisterViewIx t')} ≠ {repr (nonRegisterViewIx t)}"
  checkM state s!"{label}: indexed arm agrees with legacy" (armI == armL) s!"indexed {repr armI}, legacy {repr armL}"

def testCloseStaleExplicitKey (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 8: closeStaleExplicitKey_cases (item 333)"
  -- `_of_ek_none`: a dead register is left alone whatever follows.
  checkStaleCase state "dead-register-sibling" "? a\nb: c" 4 1 0 none (-1) 0 false
  checkStaleCase state "dead-register-value" "? a\n: b" 4 1 0 none (-1) 0 false
  -- `_of_inFlow`: in flow the hook is the identity even at a sibling.
  checkStaleCase state "live-in-flow" "? a\n[1]: b" 4 1 0 (some 0) 0 1 false
  checkStaleCase state "live-in-flow-deep" "? a\nb: c" 4 1 0 (some 0) 0 3 false
  -- The reset arm: a sibling entry at the `?`'s column, or left of it.
  checkStaleCase state "sibling-flow-key" "? a\n[1]: b" 4 1 0 (some 0) 0 0 true
  checkStaleCase state "sibling-plain-key" "? a\nz: v" 4 1 0 (some 0) 0 0 true
  checkStaleCase state "sibling-anchor" "? &p\n[1]: b" 5 1 0 (some 0) 0 0 true
  checkStaleCase state "sibling-left-of-key" "  ? a\nz: v" 6 1 0 (some 0) 2 0 true
  checkStaleCase state "sibling-quoted" "? a\n\"q\": v" 4 1 0 (some 0) 0 0 true
  -- The two exceptions: the explicit value, the sequence continuing the key.  The next key
  -- is no longer one (item 338): the hook re-reads under it, and `scanKey` overwrites.
  checkStaleCase state "explicit-value" "? a\n: b" 4 1 0 (some 0) 0 0 false
  checkStaleCase state "seq-continuation" "?\n- a\n- b\n: v" 2 1 0 (some 0) 0 0 false
  checkStaleCase state "seq-continuation-2" "?\n- a\n- b\n: v" 6 2 0 (some 0) 0 0 false
  checkStaleCase state "next-explicit-key" "? a\n? b\n: c" 4 1 0 (some 0) 0 0 true
  -- Right of the `?`: the key's own content continues.
  checkStaleCase state "deeper-content" "? a\n  b" 6 1 2 (some 0) 0 0 false
  checkStaleCase state "deeper-sibling-column" "  ? a\n    z: v" 10 1 4 (some 0) 2 0 false
  -- Same line as the `?`, and end of input: nothing to close.
  checkStaleCase state "same-line" "? a b" 4 0 4 (some 0) 0 0 false
  checkStaleCase state "end-of-input" "? a\n" 4 1 0 (some 0) 0 0 false

/-! ## Priority 9 — `stripAnchors`/`adaptForFlowContext` commute with `resolveAliases` (PR: clean before resolve)

`addAnchor` now stores `(val.stripAnchors.adaptForFlowContext).resolveAliases ps.anchors`
where it used to store `(val.resolveAliases ps.anchors).stripAnchors.adaptForFlowContext`.
`L4YAML/Algebra/Value.lean` §7 claims the two agree whenever every table value is
`Cleaned` (`cleaned_resolveAliases_comm`, via `stripAnchors_resolveAliases` and
`adaptForFlowContext_resolveAliases`), and that the table `addAnchor` builds is
`Cleaned` entry by entry (`cleaned_of_pipeline`).

**Risk:** MEDIUM on the hypothesis: without `Cleaned` the statements are FALSE
(a table value carrying an anchor is stripped by the old order and kept by the
new one; a table value with a flow indicator in a plain scalar is quoted by the
old order only).  LOW on the structural cases, but `findSome?` takes the FIRST
match, so duplicate names must resolve identically on both sides, and an absent
alias must stay an `.alias` on both.

**Audit approach:** evaluate both sides on empty / singleton / duplicate-name /
absent-alias tables and on every constructor (scalar with and without anchor,
alias, nested sequence, nested mapping with an alias key), with cleaned tables
(both equalities must hold) and with dirty tables (the unconditional statement
must be refuted, so the hypothesis is doing work).
-/

/-- A plain scalar carrying an anchor. -/
def svAnch (content anchor : String) : YamlValue :=
  .scalar { content, style := .plain, anchor := some anchor }

/-- A block sequence carrying an anchor. -/
def seqAnch (items : List YamlValue) (anchor : String) : YamlValue :=
  .sequence .block items.toArray none (some anchor)

/-- `Cleaned` decided at runtime: the pipeline is a fixpoint of the value. -/
def isCleaned (v : YamlValue) : Bool :=
  v.stripAnchors.adaptForFlowContext == v

/-- Old `addAnchor` order: resolve, then clean. -/
def resolveThenClean (v : YamlValue) (A : Array (String × YamlValue)) : YamlValue :=
  (v.resolveAliases A).stripAnchors.adaptForFlowContext

/-- New `addAnchor` order: clean, then resolve. -/
def cleanThenResolve (v : YamlValue) (A : Array (String × YamlValue)) : YamlValue :=
  (v.stripAnchors.adaptForFlowContext).resolveAliases A

/-- One instantiation of the three §7 lemmas on a table every entry of which is
    `Cleaned`: both component commutations and the composite must hold. -/
def checkCleanedComm (state : IO.Ref TestCollector) (label : String) (v : YamlValue)
    (A : Array (String × YamlValue)) : IO Unit := do
  checkM state s!"{label}: table is Cleaned (hypothesis holds)"
    (A.all fun p => isCleaned p.2) s!"{repr A}"
  checkM state s!"{label}: stripAnchors_resolveAliases"
    ((v.resolveAliases A).stripAnchors == v.stripAnchors.resolveAliases A)
    s!"{repr (v.resolveAliases A).stripAnchors} ≠ {repr (v.stripAnchors.resolveAliases A)}"
  checkM state s!"{label}: adaptForFlowContext_resolveAliases"
    ((v.resolveAliases A).adaptForFlowContext == v.adaptForFlowContext.resolveAliases A)
    s!"{repr (v.resolveAliases A).adaptForFlowContext} ≠ {repr (v.adaptForFlowContext.resolveAliases A)}"
  checkM state s!"{label}: cleaned_resolveAliases_comm (old addAnchor = new addAnchor)"
    (resolveThenClean v A == cleanThenResolve v A)
    s!"{repr (resolveThenClean v A)} ≠ {repr (cleanThenResolve v A)}"
  checkM state s!"{label}: cleaned_of_pipeline (what addAnchor stores is Cleaned)"
    (isCleaned (v.stripAnchors.adaptForFlowContext)) s!"{repr (v.stripAnchors.adaptForFlowContext)}"

/-- The hypothesis boundary: on a table with a non-`Cleaned` entry the two orders
    must DIFFER on a value that reaches the entry — otherwise `Cleaned` is dead weight. -/
def checkDirtyRefutes (state : IO.Ref TestCollector) (label : String) (v : YamlValue)
    (A : Array (String × YamlValue)) : IO Unit := do
  checkM state s!"{label}: table is NOT Cleaned" (!(A.all fun p => isCleaned p.2)) s!"{repr A}"
  checkM state s!"{label}: unconditional commutation is refuted"
    (resolveThenClean v A != cleanThenResolve v A) s!"both sides {repr (resolveThenClean v A)}"

def testCleanedResolveAliases (state : IO.Ref TestCollector) : IO Unit := do
  let a := sv "a"
  let b := sv "b"
  let tbl1 : Array (String × YamlValue) := #[("x", a)]
  let tblDup : Array (String × YamlValue) := #[("x", a), ("x", b)]
  let tblTwo : Array (String × YamlValue) := #[("x", a), ("y", seqv [a, b])]
  -- Every constructor against the empty table: nothing to substitute.
  checkCleanedComm state "empty/scalar" a #[]
  checkCleanedComm state "empty/anchored-scalar" (svAnch "a" "p") #[]
  checkCleanedComm state "empty/alias" (.alias "x") #[]
  checkCleanedComm state "empty/seq" (seqv [a, .alias "x"]) #[]
  checkCleanedComm state "empty/map" (mapv [(a, .alias "x")]) #[]
  -- Singleton table, matching alias at every position.
  checkCleanedComm state "singleton/alias" (.alias "x") tbl1
  checkCleanedComm state "singleton/alias-in-seq-first" (seqv [.alias "x", b]) tbl1
  checkCleanedComm state "singleton/alias-in-seq-last" (seqv [b, .alias "x"]) tbl1
  checkCleanedComm state "singleton/alias-as-map-key" (mapv [(.alias "x", b)]) tbl1
  checkCleanedComm state "singleton/alias-as-map-value" (mapv [(b, .alias "x")]) tbl1
  checkCleanedComm state "singleton/anchored-seq-holding-alias" (seqAnch [.alias "x"] "q") tbl1
  checkCleanedComm state "singleton/nested-seq-in-map" (mapv [(a, seqv [seqv [.alias "x"]])]) tbl1
  -- Absent alias: stays an alias on both sides.
  checkCleanedComm state "absent/alias" (.alias "nope") tbl1
  checkCleanedComm state "absent/alias-in-map" (mapv [(.alias "nope", .alias "x")]) tbl1
  -- Duplicate names: the FIRST entry wins on both sides.
  checkCleanedComm state "dup/alias" (.alias "x") tblDup
  checkCleanedComm state "dup/alias-in-seq" (seqv [.alias "x", .alias "x"]) tblDup
  checkM state "dup/first-match wins" ((YamlValue.alias "x").resolveAliases tblDup == a) ""
  -- Two names, one a collection: substituted subtree shared.
  checkCleanedComm state "two/both-aliases" (seqv [.alias "x", .alias "y"]) tblTwo
  checkCleanedComm state "two/map-of-aliases" (mapv [(.alias "x", .alias "y")]) tblTwo
  -- Plain scalar with a flow indicator: adaptForFlowContext quotes it; cleaned table keeps it quoted.
  let quoted : YamlValue := .scalar { content := "a,b", style := .doubleQuoted }
  checkCleanedComm state "flow-indicator/quoted-table" (.alias "x") #[("x", quoted)]
  checkCleanedComm state "flow-indicator/raw-value" (seqv [sv "a,b", .alias "x"]) #[("x", quoted)]
  -- Hypothesis boundary: dirty tables refute the unconditional statement.
  checkDirtyRefutes state "dirty/anchored-scalar" (.alias "x") #[("x", svAnch "a" "p")]
  checkDirtyRefutes state "dirty/anchored-seq" (seqv [.alias "x"]) #[("x", seqAnch [a] "q")]
  checkDirtyRefutes state "dirty/plain-flow-indicator" (mapv [(a, .alias "x")]) #[("x", sv "a,b")]
  checkDirtyRefutes state "dirty/second-dup-entry-unreached-still-dirty"
    (.alias "y") #[("x", a), ("y", svAnch "b" "r")]
  -- A dirty entry no alias reaches: the orders agree anyway (the refutation needs the alias).
  checkM state "dirty/unreached entry agrees"
    (resolveThenClean (.alias "x") #[("x", a), ("y", svAnch "b" "r")]
      == cleanThenResolve (.alias "x") #[("x", a), ("y", svAnch "b" "r")]) ""

/-! ## Priority 10 — `trimEndIx_eq` and the block-fold bridges (PR: drop the `List Char` round trips)

`trimEndIx p s` is the backward scan the indexed scanner runs; its spec is the
`reverse/dropWhile/reverse` round trip the proofs reason about.
`foldBlockContent` runs the fold machine with `String.foldl`; its spec is the
`List Char` recursion `foldBlockContentGo`, and `foldBlockContentGo_eq_foldl`
is the bridge at every accumulator/state/pending triple, not only the initial
one.  Each case is one equality the lemma asserts, run on the executable side. -/

/-- The `List Char` right-hand side of `trimEndIx_eq`. -/
def trimEndSpec (p : Char → Bool) (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile p).reverse)

def checkTrimEnd (state : IO.Ref TestCollector) (label : String) (p : Char → Bool) (s : String) : IO Unit :=
  checkM state s!"trimEndIx_eq/{label}" (trimEndIx p s == trimEndSpec p s)
    s!"impl {repr (trimEndIx p s)} spec {repr (trimEndSpec p s)}"

/-- `foldBlockContentGo_eq_foldl` at one `(l, acc, st, pending)` instance. -/
def checkFoldGo (state : IO.Ref TestCollector) (label : String) (l : List Char) (acc : String)
    (st : Indexed.FoldState) (pending : Nat) : IO Unit :=
  checkM state s!"foldBlockContentGo_eq_foldl/{label}"
    (foldBlockContentGo l acc st pending == foldBlockFinish (l.foldl foldBlockStep (acc, st, pending)))
    s!"go {repr (foldBlockContentGo l acc st pending)}"

/-- `foldBlockContent_eq_go` at one raw body. -/
def checkFoldContent (state : IO.Ref TestCollector) (label : String) (raw : String) : IO Unit :=
  checkM state s!"foldBlockContent_eq_go/{label}"
    (Indexed.foldBlockContent raw == foldBlockContentGo raw.toList "" .start 0)
    s!"foldl {repr (Indexed.foldBlockContent raw)} go {repr (foldBlockContentGo raw.toList "" .start 0)}"

def testScalarFinishBridges (state : IO.Ref TestCollector) : IO Unit := do
  let ws := L4YAML.CharPredicates.isWhiteSpaceBool
  let lf := L4YAML.CharPredicates.isLineFeedBool
  -- trimEndIx: empty, singleton match / non-match, all-match, trailing run, interior run kept.
  checkTrimEnd state "empty/ws" ws ""
  checkTrimEnd state "singleton/match" ws " "
  checkTrimEnd state "singleton/nonmatch" ws "a"
  checkTrimEnd state "all-match" ws "   \t "
  checkTrimEnd state "trailing-run" ws "a b \t  "
  checkTrimEnd state "trailing-nonmatch-keeps-interior" ws "a   b"
  checkTrimEnd state "leading-only" ws "   a"
  -- Multibyte: the last character is 2–4 UTF-8 bytes; `endsWith`/`dropEndWhile` must step by char.
  checkTrimEnd state "multibyte/last-nonmatch" ws "a é"
  checkTrimEnd state "multibyte/before-trailing-ws" ws "é  "
  checkTrimEnd state "multibyte/4-byte-last" ws "x 😀"
  checkTrimEnd state "multibyte/4-byte-then-tab" ws "😀\t"
  -- Line-feed predicate: the `stripTrailingNewlines` instance.
  checkTrimEnd state "lf/empty" lf ""
  checkTrimEnd state "lf/only-newlines" lf "\n\n"
  checkTrimEnd state "lf/trailing-newlines" lf "a\n\n"
  checkTrimEnd state "lf/space-after-newline-kept" lf "a\n "
  checkTrimEnd state "lf/cr-not-lf" lf "a\r"
  -- A predicate that always holds and one that never holds.
  checkTrimEnd state "const-true" (fun _ => true) "abc"
  checkTrimEnd state "const-false" (fun _ => false) "abc  "
  -- foldBlockContent_eq_go: empty, single line, trailing newline(s), folded lines, more-indented,
  -- blank lines between content, leading blank lines, lines ending in whitespace.
  checkFoldContent state "empty" ""
  checkFoldContent state "single-char" "a"
  checkFoldContent state "single-line-no-newline" "abc"
  checkFoldContent state "single-line" "abc\n"
  checkFoldContent state "two-lines-folded" "a\nb\n"
  checkFoldContent state "two-lines-no-final-newline" "a\nb"
  checkFoldContent state "blank-between" "a\n\nb\n"
  checkFoldContent state "two-blank-between" "a\n\n\nb\n"
  checkFoldContent state "leading-newline" "\na\n"
  checkFoldContent state "leading-newlines" "\n\na\n"
  checkFoldContent state "trailing-newlines" "a\n\n\n"
  checkFoldContent state "only-newlines" "\n\n"
  checkFoldContent state "more-indented-line" "a\n  b\nc\n"
  checkFoldContent state "more-indented-first" "  a\nb\n"
  checkFoldContent state "trailing-space-on-line" "a \nb\n"
  checkFoldContent state "tab-line" "\tb\n"
  checkFoldContent state "multibyte" "é\n😀\n"
  -- foldBlockContentGo_eq_foldl at non-initial accumulators: every FoldState × pending 0/1/2,
  -- with empty, newline-only, content-only, and mixed tails.
  for st in [Indexed.FoldState.start, .content, .empty, .more] do
    for pending in [0, 1, 2] do
      let tag := s!"{repr st}/pending={pending}"
      checkFoldGo state s!"{tag}/nil" [] "acc" st pending
      checkFoldGo state s!"{tag}/lf" ['\n'] "acc" st pending
      checkFoldGo state s!"{tag}/lf-lf" ['\n', '\n'] "acc" st pending
      checkFoldGo state s!"{tag}/char" ['x'] "acc" st pending
      checkFoldGo state s!"{tag}/space-char" [' ', 'x'] "acc" st pending
      checkFoldGo state s!"{tag}/char-lf-char" ['x', '\n', 'y'] "" st pending
      checkFoldGo state s!"{tag}/lf-space-char-lf" ['\n', ' ', 'x', '\n'] "acc" st pending
/-! ## Priority 11 — `AnchorIndex`: `push_inv`, `find?_eq`, `resolveAliasesWith_find?` (PR: hash-indexed anchors)

The index is built the way the parser builds it — `AnchorIndex.empty` then one
`push` per binding — and each intermediate `(map, anchors)` pair is checked
against the two conjuncts of `push_inv` for the next binding and against
`find?_eq` for every bound name, a missing name and the empty name.  Tables:
empty, singleton, the same name bound twice (first binding wins, the map keeps
the first position), two names, and a value that is itself an alias / nests
aliases, so `resolveAliasesWith idx.find?` is exercised through the index. -/

/-- Fold a table into its index, recording every intermediate pair. -/
def anchorIndexSteps (tbl : List (String × YamlValue)) :
    List ((anchors : Array (String × YamlValue)) × AnchorIndex anchors) :=
  let rec go (acc : (anchors : Array (String × YamlValue)) × AnchorIndex anchors) :
      List (String × YamlValue) → List ((anchors : Array (String × YamlValue)) × AnchorIndex anchors)
    | [] => [acc]
    | (n, v) :: rest => acc :: go ⟨acc.1.push (n, v), acc.2.push n v⟩ rest
  go ⟨#[], AnchorIndex.empty⟩ tbl

/-- The two conjuncts of `push_inv`, evaluated for `(m, anchors)` and the binding `(name, v)`
    over the query names `qs`: every mapped index is in bounds, and lookup through the
    updated map is the first-match scan of the pushed array. -/
def pushInvHolds (m : Std.HashMap String Nat) (anchors : Array (String × YamlValue))
    (name : String) (v : YamlValue) (qs : List String) : Bool :=
  let m' := if m.contains name then m else m.insert name anchors.size
  let pushed := anchors.push (name, v)
  qs.all fun n =>
    (match m'[n]? with | some i => decide (i < pushed.size) | none => true) &&
    (AnchorIndex.lookup m' pushed n == anchorsLookup pushed n)

def checkAnchorTable (state : IO.Ref TestCollector) (label : String)
    (tbl : List (String × YamlValue)) (probe : YamlValue) : IO Unit := do
  let qs : List String := (tbl.map (·.1)) ++ ["missing", ""]
  let steps := anchorIndexSteps tbl
  -- `push_inv` at every prefix, for the binding the prefix is about to receive.
  for (step, (n, v)) in steps.zip tbl do
    checkM state s!"AnchorIndex.push_inv/{label}/prefix={step.1.size}/push {n}"
      (pushInvHolds step.2.map step.1 n v qs)
      s!"map {repr step.2.map} anchors {repr step.1}"
  -- `find?_eq` and `bound` on the finished index and every prefix.
  for step in steps do
    for n in qs do
      checkM state s!"AnchorIndex.find?_eq/{label}/prefix={step.1.size}/{repr n}"
        (step.2.find? n == anchorsLookup step.1 n)
        s!"find? {repr (step.2.find? n)} scan {repr (anchorsLookup step.1 n)}"
      checkM state s!"AnchorIndex.bound/{label}/prefix={step.1.size}/{repr n}"
        (match step.2.map[n]? with | some i => decide (i < step.1.size) | none => true) ""
  -- `resolveAliasesWith_find?`: resolving through the finished index is resolving against the array.
  match steps.getLast? with
  | some fin =>
    checkM state s!"resolveAliasesWith_find?/{label}"
      (probe.resolveAliasesWith fin.2.find? == probe.resolveAliases fin.1)
      s!"via index {repr (probe.resolveAliasesWith fin.2.find?)} via array {repr (probe.resolveAliases fin.1)}"
  | none => pure ()

def testAnchorIndex (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 11: AnchorIndex push_inv / find?_eq (hash-indexed anchors)"
  let a := sv "a"
  let b := sv "b"
  let probe := mapv [(sv "k", seqv [.alias "x", .alias "y", .alias "missing", mapv [(a, .alias "x")]])]
  checkAnchorTable state "empty" [] probe
  checkAnchorTable state "singleton" [("x", a)] probe
  checkAnchorTable state "duplicate name (first wins)" [("x", a), ("x", b)] probe
  checkAnchorTable state "two names" [("x", a), ("y", b)] probe
  checkAnchorTable state "three with a duplicate in the middle" [("x", a), ("y", b), ("x", seqv [a, b])] probe
  checkAnchorTable state "alias-valued binding" [("x", a), ("y", .alias "x")] probe
  checkAnchorTable state "nested alias values" [("x", seqv [a, .alias "q"]), ("y", mapv [(b, .alias "x")])] probe
  checkAnchorTable state "empty name bound" [("", a), ("x", b)] probe
  -- The index of the empty table answers `none` for every name; `empty` is irreducible,
  -- so this is a run-time fact about the record, not an unfolding.
  for n in ["", "x", "missing"] do
    checkM state s!"AnchorIndex.empty/find? {repr n} = none"
      ((AnchorIndex.empty.find? n).isNone) ""

/-! ## Priority 12 — `FrameLevel` and the kind-selected tail (item 332)

Item 332 retyped the proof-side frame lists from `List Nat` to
`List FrameLevel {width, isSeq}`.  The lemma family claims (i) `FrameLevel.ofEntry`
is the scanner's own `IndentEntry` read as a frame (so `Covered` is literal
membership of the scanner's stack), (ii) `KeyFrames.resumeAt` / `resumeAtMap` /
`resumeAtSeq` gate on membership of the LEVEL — kind included — so a mapping
obligation at a width the list holds as a sequence is refused by membership,
never by a disjunct, and (iii) `Floor` bounds every width the frames name.

**Risk:** LOW on `width_map`/`width_seq`/`map_inj` (by `rfl`/`cases`).  MEDIUM on
the gate: if `FrameLevel.map k` and `FrameLevel.seq k` ever decided equal, or if
`ofEntry` dropped the kind, every (B2) refutation would silently become an
admission and the proofs would still compile (the kind is data the lemmas quantify
over).  Only an instantiation sees it.

**Audit approach:** scan reference inputs, project `s.indents.map FrameLevel.ofEntry`
at the deepest point and compare with the stack the input owes; decide the
membership gate on empty / singleton-map / singleton-seq / mixed frame lists; and
decide `Floor` on the same lists.
-/

open L4YAML.Proofs.IndentStackCover in
/-- The deepest frame stack the scanner holds while scanning `input`, as `FrameLevel`s —
    in the scanner's own order, bottom (the `-1` sentinel) first, innermost last. -/
def deepestFrames (input : String) (fuel : Nat := 64) : List FrameLevel := Id.run do
  let mut s := ScannerState.mk' input
  let mut best : List FrameLevel := []
  for _ in [:fuel] do
    match scanNextToken s with
    | .error _ => return best
    | .ok none => return best
    | .ok (some s') =>
      s := s'
      let fr := s.indents.toList.map FrameLevel.ofEntry
      if fr.length > best.length then best := fr
  return best

open L4YAML.Proofs.IndentStackCover in
def frameLabel (ks : List FrameLevel) : String :=
  String.intercalate ", " (ks.map fun e => s!"{if e.isSeq then "seq" else "map"} {e.width}")

open L4YAML.Proofs.IndentStackCover in
def checkFrames (state : IO.Ref TestCollector) (label input : String)
    (expected : List FrameLevel) : IO Unit := do
  let got := deepestFrames input
  checkM state s!"{label}: ofEntry projects the scanner's stack as [{frameLabel expected}]"
    (got == expected) s!"got [{frameLabel got}]"

open L4YAML.Proofs.IndentStackCover in
/-- `Floor` unfolded, so an instantiation can decide it. -/
instance (lo n : Nat) (ks : List FrameLevel) : Decidable (Floor lo n ks) :=
  inferInstanceAs (Decidable (lo ≤ n ∧ ∀ e ∈ ks, lo ≤ e.width))

open L4YAML.Proofs.IndentStackCover in
def testFrameLevelKinds (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 12: FrameLevel kinds and the membership gate (item 332)"
  -- (i) `ofEntry`: the scanner's own entries, kind included (`mk'` seeds the `-1` sentinel,
  -- a mapping entry whose width `toNat` clamps to 0).
  checkFrames state "block map" "a:\n  b: c\n"
    [FrameLevel.map 0, FrameLevel.map 0, FrameLevel.map 2]
  checkFrames state "block seq" "- a\n- b\n" [FrameLevel.map 0, FrameLevel.seq 0]
  checkFrames state "map over seq" "a:\n  - b\n" [FrameLevel.map 0, FrameLevel.map 0, FrameLevel.seq 2]
  checkFrames state "seq over map" "- a: b\n  c: d\n" [FrameLevel.map 0, FrameLevel.seq 0, FrameLevel.map 2]
  checkFrames state "flow only" "[a, b]\n" [FrameLevel.map 0]
  -- (ii) the gate `FrameLevel.map j ∈ ks` that `KeyFrames.resumeAt` / `resumeAtMap` spend,
  -- and `FrameLevel.seq j ∈ ks` for `resumeAtSeq`: decided on the boundary stacks.
  let m2 := FrameLevel.map 2; let s2 := FrameLevel.seq 2; let m0 := FrameLevel.map 0
  checkM state "empty: no level resumes" (decide (m2 ∈ ([] : List FrameLevel)) == false) "map 2 ∈ []"
  checkM state "singleton map: its own width resumes" (decide (m2 ∈ [m2]) == true) "map 2 ∉ [map 2]"
  checkM state "singleton map: another width does not" (decide (m0 ∈ [m2]) == false) "map 0 ∈ [map 2]"
  checkM state "singleton seq: the mapping gate is refused at the same width"
    (decide (m2 ∈ [s2]) == false) "map 2 ∈ [seq 2] — the (B2) refutation would be an admission"
  checkM state "singleton seq: the sequence gate admits it" (decide (s2 ∈ [s2]) == true) "seq 2 ∉ [seq 2]"
  checkM state "mixed: map gate finds the map level below a seq" (decide (m0 ∈ [s2, m0]) == true) "map 0 ∉ [seq 2, map 0]"
  checkM state "mixed: map gate refuses the seq level's width" (decide (m2 ∈ [s2, m0]) == false) "map 2 ∈ [seq 2, map 0]"
  checkM state "mixed: seq gate refuses the map level's width" (decide (FrameLevel.seq 0 ∈ [s2, m0]) == false) "seq 0 ∈ [seq 2, map 0]"
  checkM state "map k ≠ seq k" (decide (m2 = s2) == false) "map 2 = seq 2"
  checkM state "map_inj" (decide (FrameLevel.map 3 = FrameLevel.map 3) && !(decide (FrameLevel.map 3 = FrameLevel.map 4))) "map_inj"
  -- (iii) `Floor lo n ks`: `lo ≤ n` and `lo` at or below every width named, whatever the kind.
  checkM state "Floor: empty frames bound by the index alone" (decide (Floor 2 3 []) && !(decide (Floor 4 3 []))) "Floor on []"
  checkM state "Floor: a named width below lo refutes" (decide (Floor 2 5 [FrameLevel.map 1]) == false) "Floor 2 5 [map 1]"
  checkM state "Floor: a seq width counts like a map width"
    (decide (Floor 2 5 [s2, m2]) && !(decide (Floor 3 5 [s2, FrameLevel.map 4]))) "Floor on mixed kinds"

/-! ### The resume conclusions, instantiated at compile time

`KeyFrames.resumeAt` / `resumeAtMap` / `resumeAtSeq` promise, for a member level,
a surviving frame list pinned by `ResumeWidths` and a continuation of the
level's OWN kind.  Those are `Prop`s, so the instantiation is an `example` per
boundary stack (zero, one and two levels; map, seq, mixed), each of which fails
to elaborate if the statement weakens: the `ResumeWidths` reading is spent to
decide exactly which levels survive, and the continuation is applied to the
kind's own empty tail (`SCompactMapTail.nil` / `SCompactSeqTail.nil`) — the
opposite kind would not type-check. -/

section ResumeConclusions
open L4YAML.Surface L4YAML.Proofs.IndentStackCover L4YAML.Proofs.StreamAccum

/-- `[map 2]`: the trivial continuation closes at the bottom. -/
lemma kfMap2 (sp : SurfPos) : KeyFrames (fun _ => True) [FrameLevel.map 2] sp :=
  .mapLevel 2 [] sp (fun _ h => absurd h List.not_mem_nil) (fun _ _ => .bottom _ trivial)

/-- `[seq 2]`. -/
lemma kfSeq2 (sp : SurfPos) : KeyFrames (fun _ => True) [FrameLevel.seq 2] sp :=
  .seqLevel 2 [] sp (fun _ h => absurd h List.not_mem_nil) (fun _ _ => .bottom _ trivial)

/-- `[seq 2, map 0]`: a sequence level opened under a mapping level, innermost first. -/
lemma kfSeq2Map0 (sp : SurfPos) : KeyFrames (fun _ => True) [FrameLevel.seq 2, FrameLevel.map 0] sp :=
  .seqLevel 2 [FrameLevel.map 0] sp
    (fun fr h => by simp only [List.mem_singleton] at h; subst h; decide)
    (fun sp' _ => .mapLevel 0 [] sp' (fun _ h => absurd h List.not_mem_nil) (fun _ _ => .bottom _ trivial))

/-- `[map 4, map 1]`: two mapping levels. -/
lemma kfMap4Map1 (sp : SurfPos) : KeyFrames (fun _ => True) [FrameLevel.map 4, FrameLevel.map 1] sp :=
  .mapLevel 4 [FrameLevel.map 1] sp
    (fun fr h => by simp only [List.mem_singleton] at h; subst h; decide)
    (fun sp' _ => .mapLevel 1 [] sp' (fun _ h => absurd h List.not_mem_nil) (fun _ _ => .bottom _ trivial))

-- Zero levels: nothing resumes (the gate is membership of `[]`).
example : ¬ (FrameLevel.map 0 ∈ ([] : List FrameLevel)) := by decide
example : ¬ (FrameLevel.seq 0 ∈ ([] : List FrameLevel)) := by decide

-- One mapping level: resumes at its own width with NO survivor, and the
-- continuation owed is the MAP tail.
example (sp : SurfPos) : True := by
  obtain ⟨ks', hw, cont⟩ := (kfMap2 sp).resumeAtMap (j := 2) (by decide)
  have h_none : ∀ fr, fr ∉ ks' := fun fr h => by
    have ⟨hm, hlt⟩ := (hw fr).mp h
    simp only [List.mem_singleton] at hm; subst hm; exact absurd hlt (by decide)
  exact (cont sp (SCompactMapTail.nil 2 sp)).close

-- One mapping level is NOT resumable as a sequence (the opposite kind is refused by the gate).
example : ¬ (FrameLevel.seq 2 ∈ [FrameLevel.map 2]) := by decide

-- One sequence level: the SEQ tail, no survivor; not resumable as a mapping.
example (sp : SurfPos) : True := by
  obtain ⟨ks', hw, cont⟩ := (kfSeq2 sp).resumeAtSeq (j := 2) (by decide)
  have h_none : ∀ fr, fr ∉ ks' := fun fr h => by
    have ⟨hm, hlt⟩ := (hw fr).mp h
    simp only [List.mem_singleton] at hm; subst hm; exact absurd hlt (by decide)
  exact (cont sp (SCompactSeqTail.nil 2 sp)).close
example : ¬ (FrameLevel.map 2 ∈ [FrameLevel.seq 2]) := by decide

-- Mixed, resumed at the sequence level: `map 0` survives, `seq 2` does not,
-- and the survivor is itself resumable as a mapping afterwards.
example (sp : SurfPos) : True := by
  obtain ⟨ks', hw, cont⟩ := (kfSeq2Map0 sp).resumeAtSeq (j := 2) (by decide)
  have h_keep : FrameLevel.map 0 ∈ ks' := (hw _).mpr ⟨by decide, by decide⟩
  have h_drop : FrameLevel.seq 2 ∉ ks' := fun h => absurd ((hw _).mp h).2 (by decide)
  have next := cont sp (SCompactSeqTail.nil 2 sp)
  obtain ⟨ks'', hw', cont'⟩ := next.resumeAtMap (j := 0) h_keep
  have h_none : ∀ fr, fr ∉ ks'' := fun fr h => absurd ((hw' fr).mp h).2 (by omega)
  exact (cont' sp (SCompactMapTail.nil 0 sp)).close

-- Mixed, resumed at the inner mapping level directly: nothing survives (the
-- sequence level above it is not below width 0) and the tail is the MAP tail.
example (sp : SurfPos) : True := by
  obtain ⟨ks', hw, cont⟩ := (kfSeq2Map0 sp).resumeAtMap (j := 0) (by decide)
  have h_none : ∀ fr, fr ∉ ks' := fun fr h => absurd ((hw fr).mp h).2 (by omega)
  exact (cont sp (SCompactMapTail.nil 0 sp)).close

-- Two mapping levels: resuming at the outer keeps the inner; at the inner keeps nothing.
example (sp : SurfPos) : True := by
  obtain ⟨ks', hw, cont⟩ := (kfMap4Map1 sp).resumeAtMap (j := 4) (by decide)
  have h_keep : FrameLevel.map 1 ∈ ks' := (hw _).mpr ⟨by decide, by decide⟩
  have h_drop : FrameLevel.map 4 ∉ ks' := fun h => absurd ((hw _).mp h).2 (by decide)
  exact (cont sp (SCompactMapTail.nil 4 sp)).close
example (sp : SurfPos) : True := by
  obtain ⟨ks', hw, cont⟩ := (kfMap4Map1 sp).resumeAtMap (j := 1) (by decide)
  have h_none : ∀ fr, fr ∉ ks' := fun fr h => by
    have ⟨hm, hlt⟩ := (hw fr).mp h
    rcases List.mem_cons.mp hm with h | h
    · subst h; exact absurd hlt (by decide)
    · have h := List.mem_singleton.mp h; subst h; exact absurd hlt (by decide)
  exact (cont sp (SCompactMapTail.nil 1 sp)).close

end ResumeConclusions

/-! ## Priority 13 — `PendingKeys` and the re-read register (item 335, row 12 step 4)

`ScannerState.pendingKeys` runs in lockstep with `indents`: one slot per level,
`some line` while that level's explicit key is open.  The register
`explicitKeyLine`/`explicitKeyCol` is re-read off the stack whenever a level's
key closes (`PendingKeys.close`, `closeStaleExplicitKey(Ix)`), so an outer `?`
survives an inner one's value.

**Risk:** MEDIUM on the array helpers (`findSomeRev?` must pick the DEEPEST
pending level; `closeAt` must close by COLUMN and leave size alone), HIGH on the
end-to-end claim — item 333's hook used to reset the register, and the three
restated `ExplicitKeyCoupling` lemmas only say the result is "a re-read", which
holds for any re-read.  Only an instantiation sees that the re-read is the
OUTER key.

**Audit approach:** the helpers on empty / all-dead / one / nested stacks; the
hook on a two-level stack (legacy and indexed); the parser on the inputs
item 334 §3 found refused (`?⏎  ? y⏎  : z⏎: w: x` and the `? q` variant) and
their controls.
-/

def testPendingKeys (state : IO.Ref TestCollector) : IO Unit := do
  let cols : Array Int := #[0, 2, 4]
  let nested : Array (Option Nat) := #[some 0, none, some 3]
  checkM state "innermost/empty stacks" (PendingKeys.innermost #[] #[] == (none, -1)) ""
  checkM state "innermost/all dead" (PendingKeys.innermost cols #[none, none, none] == (none, -1)) ""
  checkM state "innermost/single outer" (PendingKeys.innermost cols #[some 0, none, none] == (some 0, 0)) ""
  checkM state "innermost/picks the deepest" (PendingKeys.innermost cols nested == (some 3, 4)) ""
  checkM state "closeAt/absent column is identity" (PendingKeys.closeAt cols nested 7 == nested) ""
  checkM state "closeAt/keeps the size" ((PendingKeys.closeAt cols nested 0).size == 3) ""
  checkM state "closeAt/closes by column" (PendingKeys.closeAt cols nested 4 == #[some 0, none, none]) ""
  checkM state "close/inner closed → outer re-read"
    (PendingKeys.close cols nested 4 == (#[some 0, none, none], some 0, 0)) ""
  checkM state "close/outer closed → dead"
    (PendingKeys.close cols #[some 0, none, none] 0 == (#[none, none, none], none, -1)) ""
  checkM state "close/lockstep: shorter cols → missing columns never match"
    (PendingKeys.close #[0] #[some 0, some 1] 2 == (#[some 0, some 1], some 1, -1)) ""
  -- The stale hook on a two-level stack: `z` at column 0 closes the inner `? a` (column 2)
  -- AND the outer `?` (column 0) — since item 348 the hook closes every marked level the
  -- cursor lands at or left of, so the register dies (it re-read the outer key before).
  let s0 := staleStateAt "?\n  ? a\nz: v" 8 2 0 (some 1) 2 0
  let s2 : ScannerState := { s0 with
    indents := #[{ column := -1, isSequence := false }, { column := 0, isSequence := false },
                 { column := 2, isSequence := false }],
    pendingKeys := #[none, some 0, some 1] }
  let s2' := closeStaleExplicitKey s2
  checkM state "hook/two levels: the column-0 landing kills the register (item 348)"
    ((s2'.explicitKeyLine, s2'.explicitKeyCol) == (none, -1))
    s!"({repr s2'.explicitKeyLine}, {s2'.explicitKeyCol})"
  checkM state "hook/two levels: both marked slots closed"
    (s2'.pendingKeys == #[none, none, none]) s!"{repr s2'.pendingKeys}"
  let s1 : ScannerState := { s2 with pendingKeys := #[none, none, some 1] }
  let s1' := closeStaleExplicitKey s1
  checkM state "hook/one level: register dies (item 333's arm)"
    ((s1'.explicitKeyLine, s1'.explicitKeyCol) == (none, -1)) ""
  -- `:` strictly LEFT of the stale key closes it; AT the key's column it is the value.
  let sl := { s2 with offset := 8 }
  checkM state "hook/`:` left of the key closes it"
    (((closeStaleExplicitKey { sl with input := "?\n  ? a\n: w" }).explicitKeyLine) == some 0) ""
  checkM state "hook/`:` at the key's column is its value (identity)"
    ((closeStaleExplicitKey (staleStateAt "? a\n: b" 4 1 0 (some 0) 0 0)).explicitKeyLine == some 0) ""
  -- End to end: the inputs item 334 §3 found refused, and their controls.
  let accepts (input : String) : Bool := match parseYaml input with | .ok _ => true | .error _ => false
  checkM state "parse/outer ? survives inner value" (accepts "?\n  ? y\n  : z\n: w: x\n") ""
  checkM state "parse/outer ? survives inner value and a second inner key"
    (accepts "?\n  ? y\n  : z\n  ? q\n: w: x\n") ""
  checkM state "parse/control: compact mapping key" (accepts "?\n  y: z\n: w: x\n") ""
  checkM state "parse/control: spec 8.19" (accepts "? earth: blue\n: moon: white\n") ""
  checkM state "parse/control: value left of a dead key refused (libyaml)"
    (!accepts "- a\n- ? a\n: a\n") ""
  checkM state "parse/control: item 333 main input" (accepts "? a\n[1]: b\n") ""
  -- Flow collection inside a nested explicit key: the flow `:` must leave the BLOCK
  -- pending-key slots alone (the flow open saved the register on `explicitKeyStack`
  -- and the close restores it; a cleared slot would orphan that register).
  let acceptsIx (input : String) : Bool :=
    match L4YAML.TokenParser.Indexed.parseYamlIx input with | .ok _ => true | .error _ => false
  for (label, input) in [
      ("flow map value", "?\n  ? {a: b}\n  : z\n: w: x\n"),
      ("flow seq value", "?\n  ? [a, b]\n  : z\n: w: x\n"),
      ("flow map as the inner value", "?\n  ? y\n  : {a: b}\n: w: x\n"),
      ("flow map in the outer value", "?\n  ? y\n  : z\n: {a: b}\n"),
      ("nested flow in flow", "?\n  ? {a: [b, {c: d}]}\n  : z\n: w: x\n"),
      ("single level, flow key", "? {a: b}\n: z\n")] do
    checkM state s!"parse/flow inside a nested ? — legacy: {label}" (accepts input) ""
    checkM state s!"parse/flow inside a nested ? — indexed: {label}" (acceptsIx input) ""

/-! ## Priority 14 — the `-` dedent arm of the stale-key hook (item 337, row 12)

Item 333's hook exempted `-` so that `?⏎- a⏎- b⏎: v` keeps the `?` open while
its block-sequence content runs at the key's own column.  The exemption was
too wide: a `-` strictly LEFT of the pending `?` (`- ? a⏎- b`) pops the key's
level in `unwindIndents` but left the register alive until the next content
token, so "register = innermost pending key" was false between the two.

**Risk:** HIGH on the boundary — `-` AT the key's column must stay the key's
content (identity), `-` left of it must close the key; both pipelines must
agree; and the parser movement this creates (`… - ? a⏎- : b`, previously
`misindentedExplicitValue`) must be the known `- : b` empty-key divergence and
nothing else.

**Audit approach:** the hook on a parked `?` at column 2 with the `-` at 0 and
at 2 (legacy and indexed); the three `BlockDeferralClasses` inputs that moved,
through both parsers, beside the bare `- : b` control.
-/

def testDedentHook (state : IO.Ref TestCollector) : IO Unit := do
  -- `- ? a⏎- b`: parked after the unwind to column 0, the `?`'s level (column 2) is gone.
  let dedent := "- ? a\n- b"
  let s := { staleStateAt dedent 6 1 0 (some 0) 2 0 with
    indents := #[{ column := -1, isSequence := false }, { column := 0, isSequence := true }],
    pendingKeys := #[none, none] }
  let s' := closeStaleExplicitKey s
  checkM state "hook/`-` left of the key: register dies"
    ((s'.explicitKeyLine, s'.explicitKeyCol) == (none, -1))
    s!"({repr s'.explicitKeyLine}, {s'.explicitKeyCol})"
  let t := { staleStateIxAt dedent 6 (some 0) 2 0 with
    indents := #[{ column := -1, isSequence := false }, { column := 0, isSequence := true }],
    pendingKeys := #[none, none] }
  let t' := t.closeStaleExplicitKeyIx
  checkM state "hook/`-` left of the key: register dies (indexed)"
    ((t'.explicitKeyLine, t'.explicitKeyCol) == (none, -1)) ""
  -- `?⏎- a`: the `-` AT the key's column is its content; the hook is the identity.
  let same := staleStateAt "?\n- a" 2 1 0 (some 0) 0 0
  checkM state "hook/`-` at the key's column: identity"
    ((closeStaleExplicitKey same).explicitKeyLine == some 0) ""
  checkM state "hook/`-` at the key's column: identity (indexed)"
    ((staleStateIxAt "?\n- a" 2 (some 0) 0 0).closeStaleExplicitKeyIx.explicitKeyLine == some 0) ""
  -- End to end: the movement is exactly the `- : b` divergence (libyaml refuses all four).
  let accepts (input : String) : Bool := match parseYaml input with | .ok _ => true | .error _ => false
  let acceptsIx (input : String) : Bool :=
    match L4YAML.TokenParser.Indexed.parseYamlIx input with | .ok _ => true | .error _ => false
  for (label, input) in [
      ("control: bare empty key", "- : b\n"),
      ("dedent past a compact ?", "- ? a\n- : b\n"),
      ("dedent past a compact ? with a flow key", "- ? [x]\n- : b\n"),
      ("dedent past a nested compact ?", "- - ? a\n- - : b\n"),
      ("dedent to a plain entry", "- ? a\n- b\n"),
      ("control: ? content at its own column", "?\n- a\n- b\n: v\n")] do
    checkM state s!"parse/dedent hook — legacy: {label}" (accepts input) ""
    checkM state s!"parse/dedent hook — indexed: {label}" (acceptsIx input) ""
  checkM state "parse/dedent hook — value left of a dead key still refused"
    (!accepts "- a\n- ? a\n: a\n") ""

/-! ## Priority 15 — the hook fires on `col ≤ ekCol` alone; the token-level carrier (item 338, row 12)

Item 338 proves `PendingKeySound.Sound` (register = innermost pending key
outside flow, slot 0 of `explicitKeyStack` = innermost inside, one saved pair
per flow level, marked slots on columns ≥ 0) through every `scanNextToken`
arm.  Two exemptions of the hook had to go for `preprocess_sound`: the
same-line guard (`s.line != ekLine`), which let a register outlive an unwind
that popped its level, and the `?` exemption, which left the register stale
under a `?` that is NOT a key indicator (`?x`).  A key `?` never read the
register (`scanKey` overwrites it), so for it the hook's re-read is invisible.

**Risk:** the hook must still be the identity at or right of the register
column, both pipelines must agree, and `PendingKeys.innermost` must pick the
DEEPEST marked slot (the lemma `marked_le_innermost` leans on it).

**Audit approach:** the hook under a non-key `?`, under a key `?` at the key's
own column, and with a same-line register (synthetic); `innermost` on a stack
with two marked slots and after each `closeAt`; both parsers on the inputs the
change can touch.
-/

def testHookCarrier (state : IO.Ref TestCollector) : IO Unit := do
  -- `- ? a⏎?x`: after the unwind to column 0 the `?`'s level (column 2) is gone; the next
  -- character is a `?` that is NOT a key indicator.  Item 333 exempted `?` outright and left
  -- the register alive; now it dies.
  let nonKey := "- ? a\n?x"
  let s := { staleStateAt nonKey 6 1 0 (some 0) 2 0 with
    indents := #[{ column := -1, isSequence := false }, { column := 0, isSequence := true }],
    pendingKeys := #[none, none] }
  checkM state "hook/non-key `?` left of the key: register dies"
    (((closeStaleExplicitKey s).explicitKeyLine, (closeStaleExplicitKey s).explicitKeyCol)
      == (none, -1)) ""
  let t := { staleStateIxAt nonKey 6 (some 0) 2 0 with
    indents := #[{ column := -1, isSequence := false }, { column := 0, isSequence := true }],
    pendingKeys := #[none, none] }
  checkM state "hook/non-key `?` left of the key: register dies (indexed)"
    ((t.closeStaleExplicitKeyIx.explicitKeyLine, t.closeStaleExplicitKeyIx.explicitKeyCol)
      == (none, -1)) ""
  -- `? a⏎? b`: a key `?` at the key's own column.  The hook re-reads (the slot at column 0 is
  -- the register's own, so the re-read is `(none, -1)`); `scanKey` then marks it again.
  let sibling := "? a\n? b"
  let s2 := { staleStateAt sibling 4 1 0 (some 0) 0 0 with
    indents := #[{ column := -1, isSequence := false }, { column := 0, isSequence := false }],
    pendingKeys := #[none, some 0] }
  checkM state "hook/key `?` at the key's column: slot cleared, register re-read"
    ((closeStaleExplicitKey s2).pendingKeys == #[none, none]
      && (closeStaleExplicitKey s2).explicitKeyLine == none) ""
  let t2 := { staleStateIxAt sibling 4 (some 0) 0 0 with
    indents := #[{ column := -1, isSequence := false }, { column := 0, isSequence := false }],
    pendingKeys := #[none, some 0] }
  checkM state "hook/key `?` at the key's column: slot cleared, register re-read (indexed)"
    (t2.closeStaleExplicitKeyIx.pendingKeys == #[none, none]
      && t2.closeStaleExplicitKeyIx.explicitKeyLine == none) ""
  -- Same-line register, cursor at or left of its column (unreachable by scanning; the dropped
  -- guard).  The hook now fires; before item 338 it was the identity.
  let same := { staleStateAt "? a" 0 0 0 (some 0) 2 0 with
    indents := #[{ column := -1, isSequence := false }, { column := 2, isSequence := false }],
    pendingKeys := #[none, some 0] }
  checkM state "hook/same-line register left of the cursor: fires"
    ((closeStaleExplicitKey same).explicitKeyLine == none) ""
  checkM state "hook/same-line register left of the cursor: fires (indexed)"
    (({ staleStateIxAt "? a" 0 (some 0) 2 0 with
        indents := #[{ column := -1, isSequence := false }, { column := 2, isSequence := false }],
        pendingKeys := #[none, some 0] }).closeStaleExplicitKeyIx.explicitKeyLine == none) ""
  -- Right of the register column the hook is the identity (both pipelines).
  let right := staleStateAt "? a: b" 3 0 3 (some 0) 0 0
  checkM state "hook/cursor right of the key: identity"
    ((closeStaleExplicitKey right).explicitKeyLine == some 0) ""
  checkM state "hook/cursor right of the key: identity (indexed)"
    ((staleStateIxAt "? a: b" 3 (some 0) 0 0).closeStaleExplicitKeyIx.explicitKeyLine == some 0) ""
  -- `PendingKeys.innermost` picks the DEEPEST marked slot; `closeAt` erases one column only.
  let cols : Array Int := #[-1, 0, 2]
  let pks : Array (Option Nat) := #[none, some 0, some 1]
  checkM state "innermost/two marked slots: the deepest wins"
    (PendingKeys.innermost cols pks == (some 1, 2)) s!"{repr (PendingKeys.innermost cols pks)}"
  checkM state "innermost/closeAt the deep slot: the shallow one surfaces"
    (PendingKeys.innermost cols (PendingKeys.closeAt cols pks 2) == (some 0, 0)) ""
  checkM state "innermost/closeAt the shallow slot: the deep one stays"
    (PendingKeys.innermost cols (PendingKeys.closeAt cols pks 0) == (some 1, 2)) ""
  checkM state "innermost/closeAt an unmarked column: no change"
    (PendingKeys.closeAt cols pks 7 == pks) ""
  checkM state "innermost/all slots empty: (none, -1)"
    (PendingKeys.innermost cols #[none, none, none] == (none, -1)) ""
  -- End to end: both parsers agree on every input the change can touch, and every verdict is
  -- libyaml's and the pre-item-338 binaries' (`? a⏎? b` two null-valued keys; `- ? a⏎?x` and
  -- `- ? a⏎? b` are refused by libyaml and by both pipelines before and after the change).
  let accepts (input : String) : Bool := match parseYaml input with | .ok _ => true | .error _ => false
  let acceptsIx (input : String) : Bool :=
    match L4YAML.TokenParser.Indexed.parseYamlIx input with | .ok _ => true | .error _ => false
  for (label, input, expected) in [
      ("sibling explicit keys", "? a\n? b\n", true),
      ("non-key ? after a dedent", "- ? a\n?x\n", false),
      ("key ? after a dedent", "- ? a\n? b\n", false),
      ("nested ? family (item 335)", "?\n  ? y\n  : z\n: w: x\n", true),
      ("dedent to a plain entry (item 337)", "- ? a\n- b\n", true),
      ("value left of a dead key", "- a\n- ? a\n: a\n", false)] do
    checkM state s!"parse/hook carrier — legacy: {label}" (accepts input == expected) ""
    checkM state s!"parse/hook carrier — indexed: {label}" (acceptsIx input == expected) ""

/-- `PendingKeySound.Sound`, `Mono`, `SentinelBase` and `PreprocessFloor` as Booleans, so the
    statement of `scanNextToken_sound` can be instantiated at the runtime: hypotheses on the
    pre-state, conclusion on the post-state, at every token boundary of a walk. -/
def soundB (s : ScannerState) : Bool :=
  let inn := PendingKeys.innermost s.indentColumns s.pendingKeys
  s.pendingKeys.size == s.indents.size
    && (List.range s.pendingKeys.size).all (fun i =>
          match s.pendingKeys[i]? with
          | some (some _) => (s.indentColumns[i]?.getD (-1)) ≥ 0
          | _ => true)
    && (s.flowLevel != 0 || (s.explicitKeyLine, s.explicitKeyCol) == inn)
    && (s.flowLevel == 0 || s.explicitKeyStack[0]? == some inn)
    && s.explicitKeyStack.size == s.flowLevel

def monoB (s : ScannerState) : Bool :=
  (List.range (s.indents.size - 1)).all fun i =>
    match s.indents[i]?, s.indents[i+1]? with
    | some a, some b => a.column < b.column
    | _, _ => true

def sentinelB (s : ScannerState) : Bool :=
  s.indents[0]? == some { column := -1, isSequence := false }

def preprocessFloorB (s : ScannerState) : Bool :=
  match scanNextToken_preprocess s with
  | .ok (some (sp, _)) => sp.inFlow || sp.currentIndent ≤ (sp.col : Int)
  | _ => true

/-- Walk `scanNextToken` from `mk'`; at each step check the hypotheses of `scanNextToken_sound`
    on the pre-state and its conclusion on the post-state.  Returns
    `(steps, hypothesis failures, conclusion failures)`. -/
def walkSound (input : String) : Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut steps := 0
  let mut hypFail := 0
  let mut concFail := 0
  let mut fuel := input.length + 8
  while fuel > 0 do
    fuel := fuel - 1
    let hyp := soundB s && monoB s && sentinelB s && preprocessFloorB s
    match scanNextToken s with
    | .ok (some s') =>
      steps := steps + 1
      if !hyp then hypFail := hypFail + 1
      else if !soundB s' then concFail := concFail + 1
      s := s'
    | _ => fuel := 0
  return (steps, hypFail, concFail)

def testTokenCarrierWalk (state : IO.Ref TestCollector) : IO Unit := do
  -- The seed satisfies every hypothesis.
  let s0 := ScannerState.mk' "a"
  checkM state "walk/seed: Sound ∧ Mono ∧ SentinelBase ∧ PreprocessFloor"
    (soundB s0 && monoB s0 && sentinelB s0 && preprocessFloorB s0) ""
  -- A state that REFUTES `Sound` (register alive, no marked slot) is reported as such.
  checkM state "walk/soundB refutes a stale register"
    (!soundB (staleStateAt "a" 0 0 0 (some 0) 2 0)) ""
  for (label, input) in [
      ("empty", ""),
      ("scalar", "a\n"),
      ("sibling explicit keys", "? a\n? b\n: c\n"),
      ("explicit key, dedent to `-`", "- ? a\n- b\n"),
      ("explicit key, non-key `?`", "- ? a\n?x\n"),
      ("nested ? family (item 335)", "?\n  ? y\n  : z\n: w: x\n"),
      ("? content at its own column", "?\n- a\n- b\n: v\n"),
      ("flow inside ?", "?\n  ? {a: b}\n  : z\n: w: x\n"),
      ("flow key with saved pair", "? [x]\n: b\n"),
      ("nested flow", "[? a, {b: [1, {c: d}]}, ? e]\n"),
      ("document markers", "? a\n---\nb\n...\n? c\n"),
      ("directive", "%YAML 1.2\n---\n? a\n: b\n"),
      ("compact in sequence", "- ? a\n  : b\n- c\n"),
      ("misindented value (refused)", "- a\n- ? a\n: a\n"),
      ("implicit then explicit", "a: 1\n? b\n: 2\n"),
      ("block scalar under ?", "? |\n  x\n: y\n"),
      ("quoted keys", "? \"q\"\n: 'v'\n"),
      ("anchors and tags", "? &k !!str a\n: *k\n"),
      ("comments", "? a # c\n# d\n: b\n"),
      ("deep nesting", "- - - ? a\n      : b\n")] do
    let (steps, hf, cf) := walkSound input
    checkM state s!"walk/{label}: hypotheses hold at every boundary" (hf == 0)
      s!"{hf} of {steps} boundaries"
    checkM state s!"walk/{label}: Sound after every step" (cf == 0) s!"{cf} of {steps} steps"

/-! ## Priority 16 — the column floor rides the token boundary (item 339, row 12)

Item 339 adds `ColFloor` (`needIndentCheck = false → currentIndent ≤ col`, every
saved simple key — the live one and the flow-stacked ones — at or behind the
cursor), proves it through every `scanNextToken` arm, and pays item 338's
STARVED `PreprocessFloor` premise with it (`scanNextToken_sound_colfloor`).
`StreamAccum` now threads `Sound ∧ ColFloor` through `scanNextToken_accum_step`
and `scanLoop_grammar_prod`, seeded at `scan`'s `mk'`/`streamStart`/BOM state.

**Risk:** the floor is read with `needIndentCheck = false` only, so the arms that
leave the cursor at a line start must set the flag (block scalars, document
markers), and the arms that stay on their line must not move the cursor LEFT
of the floor (the quoted/plain folds re-establish it by their own
`underIndentedScalar` gate; the flow plain loop by `[69] s-flow-line-prefix`).
The seed must satisfy it with and without a BOM.

**Audit approach:** `ColFloor` as a Boolean, checked at every token boundary of
a `scanNextToken` walk alongside the hypotheses of `scanNextToken_sound_colfloor`
(pre-state) and its conclusion (post-state), on the inputs each arm's floor
argument is about; the seed states; a hand-built state that REFUTES the floor
so the Boolean is known to be able to say no; and the in-flow under-indent that
`dispatchStructural_floor` reads off the dispatcher's refusal.
-/

def behindB (p : YamlPos) (s : ScannerState) : Bool :=
  p.line < s.line || (p.line == s.line && p.col ≤ s.col)

def colFloorB (s : ScannerState) : Bool :=
  (s.needIndentCheck || s.currentIndent ≤ (s.col : Int))
    && (!s.simpleKey.possible || behindB s.simpleKey.pos s)
    && s.simpleKeyStack.all (fun k => !k.possible || behindB k.pos s)

/-- Walk `scanNextToken` from a seed state; at each step check the hypotheses of
    `scanNextToken_sound_colfloor` on the pre-state and its conclusion on the post-state.
    Returns `(steps, hypothesis failures, conclusion failures)`. -/
def walkColFloor (s0 : ScannerState) (budget : Nat) : Nat × Nat × Nat := Id.run do
  let mut s := s0
  let mut steps := 0
  let mut hypFail := 0
  let mut concFail := 0
  let mut fuel := budget
  while fuel > 0 do
    fuel := fuel - 1
    let hyp := soundB s && monoB s && sentinelB s && colFloorB s
    match scanNextToken s with
    | .ok (some s') =>
      steps := steps + 1
      if !hyp then hypFail := hypFail + 1
      else if !(soundB s' && colFloorB s') then concFail := concFail + 1
      s := s'
    | _ => fuel := 0
  return (steps, hypFail, concFail)

/-- `scan`'s own seed: `mk'`, the `streamStart` emission, and the BOM if there is one. -/
def scanSeed (input : String) : ScannerState :=
  let s := (ScannerState.mk' input).emit .streamStart
  match s.peek? with
  | some '\uFEFF' => s.consumeBOM
  | _ => s

def testColFloorWalk (state : IO.Ref TestCollector) : IO Unit := do
  -- The seeds (`seed_colfloor`, `seed_bom_colfloor`, `seed_sound`, `seed_bom_sound`).
  checkM state "colfloor/seed: ColFloor ∧ Sound" (colFloorB (scanSeed "a") && soundB (scanSeed "a")) ""
  checkM state "colfloor/seed with BOM: ColFloor ∧ Sound"
    (colFloorB (scanSeed "\uFEFFa") && soundB (scanSeed "\uFEFFa")) ""
  -- The Boolean can say no: a cursor LEFT of its own floor, no indent check pending.
  let bad : ScannerState := { ScannerState.mk' "x" with
    indents := #[{ column := -1, isSequence := false }, { column := 4, isSequence := false }],
    pendingKeys := #[none, none], needIndentCheck := false, col := 2 }
  checkM state "colfloor/refutes: cursor left of the floor" (colFloorB bad == false) ""
  -- …and a live key AHEAD of the cursor.
  let badKey : ScannerState := { ScannerState.mk' "x" with
    simpleKey := { possible := true, tokenIndex := 0, pos := ⟨0, 0, 7⟩, endLine := 0 } }
  checkM state "colfloor/refutes: saved key ahead of the cursor" (colFloorB badKey == false) ""
  checkM state "colfloor/Behind: same line, left" (behindB ⟨0, 0, 1⟩ { ScannerState.mk' "x" with col := 3 }) ""
  checkM state "colfloor/Behind: earlier line" (behindB ⟨0, 0, 9⟩ { ScannerState.mk' "x" with line := 1 }) ""
  checkM state "colfloor/Behind: refutes later line"
    (behindB ⟨0, 2, 0⟩ { ScannerState.mk' "x" with line := 1, col := 9 } == false) ""
  -- Every arm's floor argument, at every token boundary.
  for (label, input) in [
      ("plain block scalar", "a: b\nc: d\n"),
      ("plain multi-line", "a: b\n  c\n  d\ne: f\n"),
      ("plain in flow, folded", "k: [a\n  b, c]\n"),
      ("flow mapping nested", "k: {a: [b, {c: d}],\n    e: f}\n"),
      ("double quoted folded", "a: \"x\n  y\"\nb: c\n"),
      ("single quoted folded", "a: 'x\n  y'\nb: c\n"),
      ("block scalar, newline after", "a: |\n  x\n  y\nb: c\n"),
      ("block scalar at EOF, no newline", "a: |\n  x"),
      ("block scalar header at EOF", "a: |"),
      ("folded block scalar, keep", "a: >+\n  x\n\n"),
      ("explicit key over block scalar", "? |\n  x\n: y\n"),
      ("explicit keys nested", "?\n  ? y\n  : z\n: w: x\n"),
      ("explicit key with flow key", "?\n  ? {a: b}\n  : z\n: w: x\n"),
      ("sequence of explicit keys", "- ? a\n  : b\n- ? c\n"),
      ("dedenting dash", "- ? a\n- b\n"),
      ("anchors tags alias", "? &k !!str a\n: *k\n"),
      ("documents", "%YAML 1.2\n---\na: 1\n...\n---\nb: 2\n"),
      ("comments", "? a # c\n# d\n: b\n"),
      ("deep nesting", "- - - ? a\n      : b\n"),
      ("BOM then mapping", "\uFEFFa: b\n"),
      ("empty", ""),
      ("flow sequence of implicit keys", "[a: b, c: d]\n")] do
    let (steps, hf, cf) := walkColFloor (scanSeed input) (input.length + 8)
    checkM state s!"colfloor/{label}: hypotheses hold at every boundary" (hf == 0)
      s!"{hf} of {steps} boundaries"
    checkM state s!"colfloor/{label}: Sound ∧ ColFloor after every step" (cf == 0)
      s!"{cf} of {steps} steps"
  -- `dispatchStructural_floor`: in flow the floor is read off the dispatcher's own
  -- under-indent check — content at or left of the enclosing block floor is refused,
  -- so a successful dispatch always has the floor.
  checkM state "colfloor/flow under-indent refused (`underIndentedFlowContent`)"
    (match scan "k:\n  v: [a,\n b]\n" with | .error _ => true | .ok _ => false) ""
  checkM state "colfloor/flow continuation at the floor + 1 accepted"
    (match scan "k:\n  v: [a,\n   b]\n" with | .error _ => false | .ok _ => true) ""

/-- `collectPlainScalarLoop_flow_inv`'s premise and conclusion as Booleans, read off an
    explicit `(l₀, c₀)` (the entry line and column). -/
def flowInvB (l₀ c₀ : Nat) (s : ScannerState) : Bool :=
  (s.line == l₀ && c₀ ≤ s.col) || (l₀ < s.line && s.currentIndent < (s.col : Int))

def forwardB (s s' : ScannerState) : Bool :=
  s.line < s'.line || (s'.line == s.line && s.col ≤ s'.col)

/-- A flow-context scanner state over `input` with one block level at `indentCol`. -/
def mkFlow (input : String) (indentCol : Int) : ScannerState :=
  { ScannerState.mk' input with
    flowLevel := 1
    indents := #[{ column := -1, isSequence := false }, { column := indentCol, isSequence := false }]
    pendingKeys := #[none, none] }

/-- Direct instantiations of the generic helper lemmas of `ColFloor.lean` on their own
    quantified scope: fuel 0/1/2, same-line and cross-line starts, vacuous premises counted. -/
def testColFloorHelpers (state : IO.Ref TestCollector) : IO Unit := do
  -- The flow plain loop at fuel 0, 1, 2 from a same-line start (`c₀ = col`) and from a
  -- cross-line start (`l₀ < line`, cursor past the floor), on inputs with and without a
  -- fold.  The conclusion must hold whenever the loop returns `.ok`.
  let mut vacuous := 0
  let mut checked := 0
  for (label, input, indentCol) in [
      ("plain", "ab, c]", (0 : Int)), ("folded", "a\n  b, c]", 0), ("folded twice", "a\n  b\n  c]", 0),
      ("under-indented fold", "a\nb]", 0), ("comment after fold", "a\n  # c\n  b]", 0),
      ("break first", "\n  b]", 0), ("empty", "", 0), ("deep floor", "a\n    b]", 2)] do
    let s := mkFlow input indentCol
    for fuel in [0, 1, 2, 3, input.length + 2] do
      -- same-line start
      match collectPlainScalarLoop s "" "" fuel true s.col s.inputEnd with
      | .ok r =>
        checked := checked + 1
        checkM state s!"flow_inv/{label}/fuel {fuel}/same-line: conclusion"
          (flowInvB s.line s.col r.state) s!"line {r.state.line} col {r.state.col}"
      | .error _ => vacuous := vacuous + 1
      -- cross-line start: pretend the loop entered one line earlier at column 0, with the
      -- cursor strictly past the floor (premise's second disjunct)
      let s2 := { s with line := 1, col := 3 }
      if flowInvB 0 0 s2 then
        match collectPlainScalarLoop s2 "" "" fuel true s2.col s2.inputEnd with
        | .ok r =>
          checked := checked + 1
          checkM state s!"flow_inv/{label}/fuel {fuel}/cross-line: conclusion"
            (flowInvB 0 0 r.state) s!"line {r.state.line} col {r.state.col}"
        | .error _ => vacuous := vacuous + 1
  checkM state "flow_inv: the loop returned .ok on most probes (premise not vacuous)"
    (checked ≥ 40) s!"checked {checked}, vacuous {vacuous}"
  checkM state "flow_inv: the under-indent gate did refuse at least once (vacuous arm reached)"
    (vacuous ≥ 1) s!"vacuous {vacuous}"
  -- `flowInvB` can say no.
  checkM state "flow_inv/refutes: cross-line cursor at the floor"
    (flowInvB 0 0 { mkFlow "x" 2 with line := 1, col := 2 } == false) ""
  -- The `Forward` helpers at fuel 0/1/2: `consumeExactSpaces`, `collectLineContentLoop`,
  -- `collectBlockScalarLoop`, `parseBlockHeaderLoop`, `collectCommentTextLoop`, and the
  -- single-step `consumeNewline`/`advance`/`skipWhitespace`/`scanBlockScalarSkipComment`.
  for (label, input) in [("spaces", "   x\n  y"), ("content", "abc\ndef"), ("break", "\n\n x"),
      ("crlf", "\r\nx"), ("header", "|2-  # c\n  x"), ("empty", ""), ("bom", "\uFEFF")] do
    let s := ScannerState.mk' input
    for n in [0, 1, 2, 5] do
      checkM state s!"forward/consumeExactSpaces/{label}/{n}" (forwardB s (consumeExactSpaces s n).2) ""
      checkM state s!"forward/collectLineContentLoop/{label}/{n}" (forwardB s (collectLineContentLoop s "" n).2) ""
      checkM state s!"forward/collectBlockScalarLoop/{label}/{n}"
        (forwardB s (collectBlockScalarLoop s "" n 2 s.inputEnd).2) ""
      checkM state s!"forward/parseBlockHeaderLoop/{label}/{n}"
        (forwardB s (parseBlockHeaderLoop s .clip none n).2.2) ""
      checkM state s!"forward/collectCommentTextLoop/{label}/{n}"
        (forwardB s (collectCommentTextLoop s "" n).2) ""
    checkM state s!"forward/consumeNewline/{label}" (forwardB s (consumeNewline s)) ""
    checkM state s!"forward/advance/{label}" (forwardB s s.advance) ""
    checkM state s!"forward/skipWhitespace/{label}" (forwardB s (skipWhitespace s)) ""
    checkM state s!"forward/scanBlockScalarSkipComment/{label}" (forwardB s (scanBlockScalarSkipComment s)) ""
  -- `forwardB` can say no.
  checkM state "forward/refutes: cursor moved left on its line"
    (forwardB { ScannerState.mk' "x" with col := 3 } { ScannerState.mk' "x" with col := 2 } == false) ""

/-! ## Priority 17 — the register witness, stated and seeded (item 342, row 12)

Item 342 states `RegisterWitness.AtCol`, `QuestionEntry`, `SlotWitness`,
`SlotsWitness` and `RegWitness` (`L4YAML/Proofs/Scanner/RegisterWitness.lean`):
every marked slot of `pendingKeys` — and, through `RegOk`, the live register
outside flow — names a `?` standing at the level's column in the input, with
that `?`'s `[186]` route to the stream.  `scanKey_witness` seeds it: the `?`
just scanned is the witness.  Item 341 predicted the one place the invariant
could fail is a level popped and re-marked at the same column (`- ? a⏎- ? b`).

**Risk:** the witness is stated on the column and the input suffix only (the
register's LINE has no cursor bridge, see the module docstring), so a `?` at the
right column on the WRONG line would satisfy it — the Boolean below checks the
line too, which is stricter than the statement, so a pass here is a pass there.
The seed must hold with and without a push (`pushMappingIndent` pushes only when
the `?` is right of the current indent), and `pushMappingIndent_getElem?_of_lt`
must be the identity below the top in both arms.

**Audit approach:** the witness as a Boolean (register, every marked slot, and
every flow-saved pair name a `?` at (line, col) of the input), checked after
every `scanNextToken` step on item 338/339's probes plus item 341's suspects; a
hand-built state that REFUTES it; the helper lemmas instantiated at the runtime
on a stack with and without a push, at the bottom slot and at the top.
-/

/-- The character at (0-based) line `l`, column `c` of `input`, lines split on `\n`. -/
def charAtLineCol (input : String) (l c : Nat) : Option Char :=
  match (input.splitOn "\n")[l]? with
  | some line => line.toList[c]?
  | none => none

/-- A register-shaped pair names a `?` in the input (`none` names nothing). -/
def pairNamesQuestion (input : String) (p : Option Nat × Int) : Bool :=
  match p with
  | (some l, c) => c ≥ 0 && charAtLineCol input l c.toNat == some '?'
  | (none, _) => true

/-- `SlotsWitness ∧ RegWitness` (and lane (d)'s saved pairs) at the runtime, with the LINE
    checked as well — stricter than the statement. -/
def witnessB (s : ScannerState) : Bool :=
  (s.flowLevel != 0 || pairNamesQuestion s.input (s.explicitKeyLine, s.explicitKeyCol))
  && (List.range s.pendingKeys.size).all (fun i =>
        match s.pendingKeys[i]? with
        | some (some l) => pairNamesQuestion s.input (some l, s.indentColumns[i]?.getD (-1))
        | _ => true)
  && s.explicitKeyStack.all (pairNamesQuestion s.input)

/-- Even inside flow the register itself names a `?`. -/
def witnessStrictB (s : ScannerState) : Bool :=
  witnessB s && pairNamesQuestion s.input (s.explicitKeyLine, s.explicitKeyCol)

/-- Walk `scanNextToken` from `mk'`; count the post-states that refute the witness and the
    ones that refute only its strict form.  Returns `(steps, failures, strict-only failures)`. -/
def walkWitness (input : String) : Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut steps := 0
  let mut fails := 0
  let mut strictFails := 0
  let mut fuel := input.length + 8
  while fuel > 0 do
    fuel := fuel - 1
    match scanNextToken s with
    | .ok (some s') =>
      steps := steps + 1
      if !witnessB s' then fails := fails + 1
      else if !witnessStrictB s' then strictFails := strictFails + 1
      s := s'
    | _ => fuel := 0
  return (steps, fails, strictFails)

def testRegisterWitnessWalk (state : IO.Ref TestCollector) : IO Unit := do
  -- The seed: no slot is marked, the register is dead.
  checkM state "witness/seed: mk' holds the witness" (witnessStrictB (ScannerState.mk' "? a\n")) ""
  checkM state "witness/seed with BOM" (witnessStrictB (scanSeed "\uFEFF? a\n")) ""
  -- A state that REFUTES the witness: a live register whose column holds `a`, not `?`.
  checkM state "witness/refuted by a register naming a non-`?`"
    (!witnessB (staleStateAt "a: b\n" 0 0 0 (some 0) 0 0)) ""
  -- …and one whose register names a `?` on the WRONG line.
  checkM state "witness/refuted by a register on the wrong line"
    (!witnessB (staleStateAt "a\n? b\n" 0 0 0 (some 0) 0 0)) ""
  -- A marked slot at a column that holds no `?` refutes the slot half.
  let s0 := ScannerState.mk' "- a\n"
  let marked := { s0 with indents := s0.indents.push { column := 0, isSequence := true },
                          pendingKeys := s0.pendingKeys.push (some 0) }
  checkM state "witness/refuted by a marked slot naming `-`" (!witnessB marked) ""
  for (label, input) in [
      ("empty", ""), ("scalar", "a\n"),
      ("sibling explicit keys", "? a\n? b\n: c\n"),
      ("explicit key, dedent to `-`", "- ? a\n- b\n"),
      ("explicit key, non-key `?`", "- ? a\n?x\n"),
      ("nested ? family (item 335)", "?\n  ? y\n  : z\n: w: x\n"),
      ("? content at its own column", "?\n- a\n- b\n: v\n"),
      ("flow inside ?", "?\n  ? {a: b}\n  : z\n: w: x\n"),
      ("flow key with saved pair", "? [x]\n: b\n"),
      ("nested flow", "[? a, {b: [1, {c: d}]}, ? e]\n"),
      ("document markers", "? a\n---\nb\n...\n? c\n"),
      ("directive", "%YAML 1.2\n---\n? a\n: b\n"),
      ("compact in sequence", "- ? a\n  : b\n- c\n"),
      ("misindented value (refused)", "- a\n- ? a\n: a\n"),
      ("implicit then explicit", "a: 1\n? b\n: 2\n"),
      ("block scalar under ?", "? |\n  x\n: y\n"),
      ("quoted keys", "? \"q\"\n: 'v'\n"),
      ("anchors and tags", "? &k !!str a\n: *k\n"),
      ("comments", "? a # c\n# d\n: b\n"),
      ("deep nesting", "- - - ? a\n      : b\n"),
      ("plain block scalar", "a: b\nc: d\n"),
      ("plain multi-line", "a: b\n  c\n  d\ne: f\n"),
      ("plain in flow, folded", "k: [a\n  b, c]\n"),
      ("flow mapping nested", "k: {a: [b, {c: d}],\n    e: f}\n"),
      ("double quoted folded", "a: \"x\n  y\"\nb: c\n"),
      ("single quoted folded", "a: 'x\n  y'\nb: c\n"),
      ("block scalar, newline after", "a: |\n  x\n  y\nb: c\n"),
      ("block scalar at EOF, no newline", "a: |\n  x"),
      ("block scalar header at EOF", "a: |"),
      ("folded block scalar, keep", "a: >+\n  x\n\n"),
      ("sequence of explicit keys", "- ? a\n  : b\n- ? c\n"),
      ("documents", "%YAML 1.2\n---\na: 1\n...\n---\nb: 2\n"),
      ("BOM then mapping", "\uFEFFa: b\n"),
      ("flow sequence of implicit keys", "[a: b, c: d]\n"),
      ("key ? after a dedent", "- ? a\n? b\n"),
      -- item 341's suspect and the boundary cases around it
      ("pop and re-mark at the same column", "- ? a\n- ? b\n"),
      ("flow key, compact value", "? [a]: b\n"),
      ("? then `---`", "? a\n---\nb\n"), ("? then `...`", "? a\n...\n"),
      ("? at col 2, dedent key at EOF", "- ? a\n? b"),
      ("`?` keys inside the flow key", "? [? a, ? b]\n: c\n"),
      ("nested flow saved pairs", "? {? a: b, ? c: [? d]}\n: e\n"),
      ("tab after ?", "?\ta\n"), ("? at EOF", "?"), ("? newline only", "?\n"),
      ("siblings with values", "? a\n: b\n? c\n: d\n"),
      ("CRLF", "? a\r\n: b\r\n"),
      ("multibyte before the ?", "é: 1\n? ü\n: v\n"),
      ("non-key ?x at col 0 after a key", "? a\n?x\n")] do
    let (steps, fails, strict) := walkWitness input
    checkM state s!"witness/{label}: holds after every step" (fails == 0)
      s!"{fails} of {steps} steps"
    checkM state s!"witness/{label}: register names a `?` even in flow" (strict == 0)
      s!"{strict} of {steps} steps"

/-! ### The statements themselves, instantiated (follow-up to the walk)

The walk above is a Boolean over scanner FIELDS: it can refute "the register
names a `?`", not the two halves of `QuestionEntry` that are propositions over
derivations — `AtCol`'s suffix and the `[186]` route to the stream.  Those are
instantiated here on the statements as written: each relation shown to hold on a
concrete position and to be REFUTED on a wrong one, the route shown to be
CONSUMED (a `QuestionEntry` whose route is false cannot produce the stream a
concrete `explicitEmpty` entry demands), and `scanKey_witness` applied to the
seed state with every premise discharged and its conclusion read at the marked
slot. -/

section WitnessInstantiations
open L4YAML.Proofs.RegisterWitness L4YAML.Surface L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.PendingKeySound L4YAML.Proofs.IndentStackBase

/-- `AtCol` holds at the input's own start. -/
example : AtCol (String.ofList ['?', ' ', 'a']) 0 ⟨['?', ' ', 'a'], 0⟩ := ⟨rfl, [], by simp⟩

/-- …and one character in, at column 1. -/
example : AtCol (String.ofList ['?', ' ', 'a']) 1 ⟨[' ', 'a'], 1⟩ := ⟨rfl, ['?'], by simp⟩

/-- REFUTED on the wrong column. -/
example : ¬ AtCol (String.ofList ['?', ' ', 'a']) 1 ⟨['?', ' ', 'a'], 0⟩ :=
  fun h => absurd h.1 (by decide)

/-- REFUTED when `sp` is not a suffix of the input (`['x']` ends in `x`, the input in `a`). -/
example : ¬ AtCol (String.ofList ['?', ' ', 'a']) 0 ⟨['x'], 0⟩ :=
  fun ⟨_, _pre, h⟩ => by
    have := congrArg List.getLast? h
    simp at this

/-- `QuestionEntry` is REFUTED when the position reads anything but `?`. -/
example (sp_start : SurfPos) : ¬ QuestionEntry (String.ofList ['a']) sp_start 0 ⟨['a'], 0⟩ :=
  fun ⟨_, ⟨_, hg⟩, _⟩ => nomatch hg

/-- `QuestionEntry` holds at a `?` with its landing — the SHAPE of the witness; the landing
    is instantiated on real derivations below (`landingQ`, `landingQ1`). -/
example (rest : List Char) (sp_start : SurfPos)
    (h_land : QuestionLanding sp_start 0 ⟨'?' :: rest, 0⟩) :
    QuestionEntry (String.ofList ('?' :: rest)) sp_start 0 ⟨'?' :: rest, 0⟩ :=
  ⟨⟨rfl, [], by simp⟩, ⟨_, GLit.mk rest 0⟩, h_land⟩

/-- The empty stream: `[211]` with no prefix, no document, no suffix — the landing at the
    first line of the input. -/
lemma streamNil (sp : SurfPos) : SLYamlStream sp sp :=
  SLYamlStream.single sp sp sp sp (GStar.nil _) (GOpt.none _) (GStar.nil _)

/-- `QuestionLanding` HELD at the first `?` of `?⏎` (column 0, the empty stream before it). -/
lemma landingQ : QuestionLanding ⟨['?', '\n'], 0⟩ 0 ⟨['?', '\n'], 0⟩ :=
  ⟨_, streamNil _, rfl, SIndent.zero _⟩

/-- …and one space in, ` ?⏎` (column 1 — the nested shape `question_open_map` lands with
    `k = 1`). -/
lemma landingQ1 : QuestionLanding ⟨[' ', '?', '\n'], 0⟩ 1 ⟨['?', '\n'], 1⟩ :=
  ⟨_, streamNil _, rfl, SIndent.succ 0 _ 0 _ (SIndent.zero _)⟩

/-- `QuestionLanding` REFUTED: no line position is one space before column 0. -/
example (sp_start : SurfPos) : ¬ QuestionLanding sp_start 1 ⟨['?'], 0⟩ :=
  fun ⟨_, _, _, h⟩ => nomatch h

/-- The landing is CONSUMED: a `QuestionEntry` at column 0 puts the stream at the `?` itself
    (`SIndent 0` is the identity), with nothing about the entry assumed. -/
example (sp_start : SurfPos)
    (hq : QuestionEntry (String.ofList ['?', '\n']) sp_start 0 ⟨['?', '\n'], 0⟩) :
    SLYamlStream sp_start ⟨['?', '\n'], 0⟩ :=
  let ⟨_, hs, _, hi⟩ := hq.2.2
  match hi with
  | SIndent.zero _ => hs

/-- `s-l-comments` across the break of a line ending at column 1: no comment, the line
    feed, no further comment lines. -/
lemma sslBreak1 (rest : List Char) : SSLComments ⟨'\n' :: rest, 1⟩ ⟨rest, 0⟩ :=
  SSLComments.withComment _ _ _ (SSBComment.noSep _ _ (SBComment.break _ _ (SBBreak.lf rest 1)))
    (GStar.nil _)

/-- The `[186]` entry `?⏎` opens, built from its characters: `?`, then an EMPTY key
    (`e-node` + `s-l-comments`), ending at the end of input. -/
lemma entryQ : SBlockMapEntry 0 ⟨['?', '\n'], 0⟩ ⟨[], 0⟩ :=
  SBlockMapEntry.explicitEmpty 0 _ ⟨['\n'], 1⟩ _ (GLit.mk ['\n'] 0)
    (SBlockIndented.empty 0 .blockOut _ _ (sslBreak1 []))

/-- The `[186]` entry `?⏎:⏎` opens, built from its characters: `?`, empty key, `:`,
    empty value (`explicit`, both nodes `e-node`). -/
lemma entryQC : SBlockMapEntry 0 ⟨['?', '\n', ':', '\n'], 0⟩ ⟨[], 0⟩ :=
  SBlockMapEntry.explicit 0 _ ⟨['\n', ':', '\n'], 1⟩ ⟨[':', '\n'], 0⟩ ⟨[':', '\n'], 0⟩ ⟨['\n'], 1⟩ _
    (GLit.mk _ 0)
    (SBlockIndented.empty 0 .blockOut _ _ (sslBreak1 [':', '\n']))
    (SIndent.zero _) (GLit.mk ['\n'] 0)
    (SBlockIndented.empty 0 .blockOut _ _ (sslBreak1 []))

/-- The whole stream `?⏎`: one bare document, a block mapping at indent 0 with `entryQ` —
    the route's conclusion at `entryQ`'s endpoint, established from the characters. -/
lemma streamQ : SLYamlStream ⟨['?', '\n'], 0⟩ ⟨[], 0⟩ :=
  SLYamlStream.single _ _ _ _ (GStar.nil _)
    (GOpt.some _ _ (SLAnyDocument.bare _ _ (SLBareDocument.mk _ _
      (SBlockNode.blockMap 0 .blockIn 0 _ _ _ _ (GOpt.none _)
        (SSLComments.startOfLine _ _ (GStar.nil _))
        (SBlockMapEntries.single 0 _ _ _ (SIndent.zero _) entryQ)))))
    (GStar.nil _)

/-- …and the whole stream `?⏎:⏎`, the same way over `entryQC`. -/
lemma streamQC : SLYamlStream ⟨['?', '\n', ':', '\n'], 0⟩ ⟨[], 0⟩ :=
  SLYamlStream.single _ _ _ _ (GStar.nil _)
    (GOpt.some _ _ (SLAnyDocument.bare _ _ (SLBareDocument.mk _ _
      (SBlockNode.blockMap 0 .blockIn 0 _ _ _ _ (GOpt.none _)
        (SSLComments.startOfLine _ _ (GStar.nil _))
        (SBlockMapEntries.single 0 _ _ _ (SIndent.zero _) entryQC)))))
    (GStar.nil _)

/-- The stream-closing half item 342 had put in the witness is the CONSUMER's: from the
    landing (`landingQ`) and the entry (`entryQ`/`entryQC`) the whole stream exists
    (`streamQ`, `streamQC`) — item 343 moved it out of `QuestionEntry` because the `?`
    landing holds `landingQ`'s facts and not these. -/
example : SLYamlStream ⟨['?', '\n'], 0⟩ ⟨[], 0⟩ ∧ SLYamlStream ⟨['?', '\n', ':', '\n'], 0⟩ ⟨[], 0⟩ :=
  ⟨streamQ, streamQC⟩

/-- A two-level stack whose top slot is marked and whose register reads it. -/
def twoLevelMarked : ScannerState :=
  { ScannerState.mk' (String.ofList ['?', ' ', 'a']) with
    indents := #[{ column := -1, isSequence := false }, { column := 0, isSequence := false }],
    pendingKeys := #[none, some 0], explicitKeyLine := some 0, explicitKeyCol := 0 }

/-- `regWitness_of_slots` on that stack: the register `(some 0, 0)` is paid by the slot
    witness at index 1 (`RegOk` decided on the concrete arrays). -/
example (sp_start : SurfPos) (sp_q : SurfPos)
    (hq : QuestionEntry (String.ofList ['?', ' ', 'a']) sp_start 0 sp_q) :
    RegWitness (String.ofList ['?', ' ', 'a']) twoLevelMarked sp_start := by
  refine regWitness_of_slots (fun _ => ?_) ?_
  · show ((some 0 : Option Nat), (0 : Int)) =
      PendingKeys.innermost twoLevelMarked.indentColumns twoLevelMarked.pendingKeys
    rw [innermost_eq_go]; simp [go, twoLevelMarked, ScannerState.indentColumns]
  · intro i l hi
    match i, hi with
    | 1, hi =>
      have hl : l = 0 := by simp [twoLevelMarked] at hi; omega
      subst hl
      exact ⟨0, sp_q, by simp [twoLevelMarked, ScannerState.indentColumns], hq⟩
    | 0, hi => simp [twoLevelMarked] at hi
    | _ + 2, hi => simp [twoLevelMarked] at hi

/-- `scanKey_witness` on the seed state of `? a⏎`: every premise discharged on the
    concrete state (`initial_corr` for the correspondence, `mk'_sound` for the slots,
    `mk'_base` for the sentinel, `decide` for the floor and the peeked `?`), the landing
    the `?` producer holds; the conclusion read at the marked slot gives a `QuestionEntry`
    whose landing is that premise. -/
example (sp_start : SurfPos) (s' : ScannerState)
    (hok : scanKey (ScannerState.mk' (String.ofList ['?', ' ', 'a', '\n'])) = .ok s')
    (h_land : QuestionLanding sp_start 0 ⟨['?', ' ', 'a', '\n'], 0⟩) :
    SlotsWitness (String.ofList ['?', ' ', 'a', '\n']) s' sp_start ∧
    (∀ l, s'.pendingKeys[1]? = some (some l) →
      ∃ (c : Nat) (sp_q : SurfPos), s'.indentColumns[1]? = some (c : Int) ∧
        QuestionEntry (String.ofList ['?', ' ', 'a', '\n']) sp_start c sp_q) := by
  have hcorr : ScannerSurfCorr (ScannerState.mk' (String.ofList ['?', ' ', 'a', '\n']))
      ⟨['?', ' ', 'a', '\n'], 0⟩ :=
    initial_corr _ _ (chars_from_zero_toList _)
  have hw : SlotsWitness (String.ofList ['?', ' ', 'a', '\n']) s' sp_start :=
    scanKey_witness hcorr rfl hok (mk'_sound _).slots (mk'_base _) (by decide) (by decide)
      h_land (fun i l hi => by
        rcases i with _ | i
        · simp [ScannerState.mk'] at hi
        · simp [ScannerState.mk'] at hi)
  exact ⟨hw, fun l hi => hw 1 l hi⟩

/-- `scanNextToken_witness` on the seed of `? a⏎` (item 343): every premise discharged on
    the concrete state (`initial_corr`, `mk'_sound`, `mk'_mono`, `mk'_base`, the floor from
    `mk'_colfloor`), the landing the `?` step owes taken as `h_land` — the SHAPE of the step;
    `StepLanding` itself is paid where the loop threads it (item 344), the two halves it is
    built from (`landingQ`, `streamNil`) are instantiated above. -/
example (sp_start : SurfPos) (s' : ScannerState)
    (hok : scanNextToken (ScannerState.mk' (String.ofList ['?', ' ', 'a', '\n'])) = .ok (some s'))
    (h_land : StepLanding (ScannerState.mk' (String.ofList ['?', ' ', 'a', '\n'])) sp_start) :
    SlotsWitness (String.ofList ['?', ' ', 'a', '\n']) s' sp_start :=
  scanNextToken_witness hok (initial_corr _ _ (chars_from_zero_toList _)) (mk'_sound _)
    (L4YAML.Proofs.IndentStackMono.mk'_mono _) (mk'_base _)
    (L4YAML.Proofs.ColFloor.preprocessFloor (L4YAML.Proofs.ColFloor.mk'_colfloor _) (mk'_base _))
    (fun i l hi => by
      rcases i with _ | i
      · simp [ScannerState.mk'] at hi
      · simp [ScannerState.mk'] at hi)
    h_land

end WitnessInstantiations

/-- Direct instantiations of the helper lemmas of `RegisterWitness.lean` at the runtime. -/
def testRegisterWitnessHelpers (state : IO.Ref TestCollector) : IO Unit := do
  -- `pushMappingIndent_getElem?_of_lt`, both arms: a push (col right of the indent) and
  -- no push (col at the indent), read at the bottom slot and at the old top.
  let base := ScannerState.mk' "x"
  let two := { base with indents := base.indents.push { column := 0, isSequence := false },
                         pendingKeys := base.pendingKeys.push (some 0) }
  for (label, col) in [("push", (2 : Int)), ("no push", 0)] do
    let pm := pushMappingIndent two col
    for i in [0, 1] do
      checkM state s!"witness/pushMappingIndent {label}: slot {i} unchanged"
        (pm.pendingKeys[i]? == two.pendingKeys[i]?) ""
      checkM state s!"witness/pushMappingIndent {label}: column {i} unchanged"
        (pm.indentColumns[i]? == two.indentColumns[i]?) ""
    checkM state s!"witness/pushMappingIndent {label}: sizes in lockstep"
      (pm.pendingKeys.size == pm.indents.size) ""
  -- `regWitness_of_slots`'s core (`innermost_some_mem`): when the register is live outside
  -- flow it is one of the marked slots' pairs — on every post-state of the walk.
  let mut checked := 0
  for input in ["? a\n? b\n: c\n", "- ? a\n- ? b\n", "?\n  ? y\n  : z\n: w: x\n", "- ? a\n? b\n"] do
    let mut s := ScannerState.mk' input
    let mut fuel := input.length + 8
    while fuel > 0 do
      fuel := fuel - 1
      match scanNextToken s with
      | .ok (some s') =>
        if s'.flowLevel == 0 then
          match s'.explicitKeyLine with
          | some l =>
            checked := checked + 1
            let slots := (List.range s'.pendingKeys.size).filter fun i =>
              s'.pendingKeys[i]? == some (some l)
                && (s'.indentColumns[i]?.getD (-1)) == s'.explicitKeyCol
            checkM state s!"witness/register is a marked slot's pair ({input.quote}, line {l})"
              (!slots.isEmpty) ""
          | none => pure ()
        s := s'
      | _ => fuel := 0
  checkM state "witness/register-slot check fired" (checked > 0) s!"{checked}"
  -- `scanKey_witness` at the runtime: scanning a `?` outside flow marks the top slot at the
  -- `?`'s column and the register names it — with a push (`? a`) and without (the second `?`
  -- of `? a⏎? b`, which re-marks the level the hook just cleared).
  for (label, input, offset, line, col) in [("push", "? a\n", 0, 0, 0), ("sibling", "? a\n? b\n", 4, 1, 0)] do
    let s := { ScannerState.mk' input with offset := offset, line := line, col := col,
                                           indents := if offset == 0 then (ScannerState.mk' input).indents
                                             else (ScannerState.mk' input).indents.push { column := 0, isSequence := false },
                                           pendingKeys := if offset == 0 then (ScannerState.mk' input).pendingKeys
                                             else (ScannerState.mk' input).pendingKeys.push none }
    -- the lemma's premises on the pre-state, counted apart from its conclusion
    let premises := !s.inFlow && s.peek? == some '?' && s.currentIndent ≤ (s.col : Int)
      && s.pendingKeys.size == s.indents.size
    checkM state s!"witness/scanKey {label}: premises hold (not vacuous)" premises ""
    match scanKey s with
    | .ok s' =>
      checkM state s!"witness/scanKey {label}: register names the `?`"
        ((s'.explicitKeyLine, s'.explicitKeyCol) == (some line, (col : Int))
          && witnessStrictB s') ""
      checkM state s!"witness/scanKey {label}: top slot marked at the `?`'s column"
        (s'.pendingKeys[s'.pendingKeys.size - 1]? == some (some line)
          && s'.indentColumns[s'.indents.size - 1]? == some (col : Int)) ""
    | .error _ => checkM state s!"witness/scanKey {label}: scans" false ""

/-! ## Priority 18 — maximal property leaves: `collectAnchorNameLoop_prod` and the `GNot` lookahead (N1a)

`[101]`/`[104]` now end an anchor/alias name with `GNot (GChar isNsAnchorChar)` and the
primary tag suffix `[99]` is `ns-tag-char+` (`L4YAML/Surface/Basic.lean`,
`L4YAML/Surface/Scalars.lean`).  `collectAnchorNameLoop_prod`
(`L4YAML/Proofs/Production/StructureProduction.lean`) carries the lookahead to the
scanner under the new premise `inputEnd - offset ≤ fuel`: the loop stops only at end
of input or at a non-anchor char.

**Risk:** the premise is load-bearing — with too little fuel the loop stops MID-name, the
landing is followed by an anchor char and `GNot` is false.  The grid below separates
**failed-hypothesis** (fuel below the remaining input) from **theorem-holds** (fuel at or
above it), on empty / singleton / multi-char names and on every terminator kind.
`scanAnchorOrAlias_prod`'s new conjuncts (`sp_mid ≠ sp'`, `GNot`) are checked through
`scanAnchorOrAlias` itself; `"&"`/`"& a"` are the `GPlus` refuters (`emptyAnchorName`).
-/

/-- `[102] ns-anchor-char` as the scanner tests it (`collectAnchorNameLoop`'s guard). -/
def anchorCharB (c : Char) : Bool :=
  !L4YAML.CharPredicates.isFlowIndicatorBool c && !L4YAML.CharPredicates.isWhiteSpaceBool c
    && !L4YAML.CharPredicates.isLineBreakBool c && L4YAML.CharPredicates.isPrintableBool c
    && c != '\uFEFF'

/-- `GNot (GChar isNsAnchorChar)` at the scanner's landing: end of input or a non-anchor char. -/
def gnotAnchorAtB (s : ScannerState) : Bool :=
  match s.peek? with
  | none => true
  | some c => !anchorCharB c

/-- One instance of `collectAnchorNameLoop_prod` from the state `s` with `fuel`:
    `(hypothesis held, GNot at the landing, name unchanged ↔ position unchanged)`. -/
def anchorLoopInstance (s : ScannerState) (fuel : Nat) : Bool × Bool × Bool :=
  let (name, s') := collectAnchorNameLoop s "" fuel
  (decide (s.inputEnd - s.offset ≤ fuel), gnotAnchorAtB s',
   (decide (s'.offset = s.offset)) == (name == ""))

/-- The remaining input of `input` seen as an anchor-name position (offset 0). -/
def nameState (input : String) : ScannerState := ScannerState.mk' input

def testMaximalPropertyLeaves (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 18: maximal property leaves (collectAnchorNameLoop_prod, N1a)"
  -- Fuel grid at `"xa]"`: the remaining input is 3 bytes.
  for fuel in [0, 1, 2, 3, 4] do
    let (hyp, gnot, stable) := anchorLoopInstance (nameState "xa]") fuel
    -- The statement: hypothesis → conclusion.
    checkM state s!"anchorLoop/\"xa]\" fuel={fuel}: hyp → GNot ∧ name/position agree"
      (!hyp || (gnot && stable)) s!"hyp={hyp} gnot={gnot} stable={stable}"
    -- Record which bucket the row is in, so a vacuous pass is visible.
    checkM state s!"anchorLoop/\"xa]\" fuel={fuel}: bucket = {if hyp then "theorem-holds" else "failed-hypothesis"}"
      (hyp == decide (3 ≤ fuel)) ""
  -- Below the bound the loop stops mid-name and the lookahead is FALSE: the premise is load-bearing.
  checkM state "anchorLoop/\"xa]\" fuel=0: lookahead refuted without the fuel premise"
    (!(anchorLoopInstance (nameState "xa]") 0).2.1) ""
  checkM state "anchorLoop/\"xa]\" fuel=1: lookahead refuted without the fuel premise"
    (!(anchorLoopInstance (nameState "xa]") 1).2.1) ""
  -- Names: empty / singleton / multi; terminators: every kind, and end of input.
  for input in ["", "x", "xa", "xa]", "x,", "x}", "x ", "x\t", "x\n", "x\r\n", "x{", "x[",
                "xa\uFEFF", "x: y", "x#c", "xa b", "]", " x"] do
    let s := nameState input
    let fuel := s.inputEnd - s.offset
    let (hyp, gnot, stable) := anchorLoopInstance s fuel
    checkM state s!"anchorLoop/{repr input}: holds at fuel = remaining input"
      (hyp && gnot && stable) s!"gnot={gnot} stable={stable}"
    let (hyp', gnot', stable') := anchorLoopInstance s (fuel + 1)
    checkM state s!"anchorLoop/{repr input}: holds with surplus fuel"
      (hyp' && gnot' && stable') ""
  -- `scanAnchorOrAlias_prod`: marker, non-empty maximal name, lookahead, the pushed token.
  for (marker, isAnchor) in [('&', true), ('*', false)] do
    -- `:` is an `[102] ns-anchor-char` (ns-char minus the flow indicators): `&a: 1` names `a:`.
    for (name, tail) in [("x", ""), ("xa", "]"), ("x", " "), ("x", ","), ("x", "\n"), ("a-b_c", " 1"),
                         ("a:", " 1"), ("a:b", ""), ("x", "{"), ("x", "}"), ("x", "[")] do
      let input := s!"{marker}{name}{tail}"
      match scanAnchorOrAlias (ScannerState.mk' input) isAnchor with
      | .ok s' =>
        let tok := s'.tokens.back?.map (·.val)
        let expected : YamlToken := if isAnchor then .anchor name else .alias name
        checkM state s!"scanAnchorOrAlias/{repr input}: maximal name token"
          (tok == some expected) s!"got {repr tok}"
        checkM state s!"scanAnchorOrAlias/{repr input}: GNot at the landing"
          (gnotAnchorAtB s') ""
        checkM state s!"scanAnchorOrAlias/{repr input}: sp_mid ≠ sp' (name non-empty)"
          (s'.offset > 1) ""
      | .error e =>
        checkM state s!"scanAnchorOrAlias/{repr input}: accepted" false s!"{repr e}"
    -- The `GPlus` refuters: no name at all.
    for input in [s!"{marker}", s!"{marker} a", s!"{marker}]", s!"{marker}\n"] do
      checkM state s!"scanAnchorOrAlias/{repr input}: refused (empty name)"
        (match scanAnchorOrAlias (ScannerState.mk' input) isAnchor with
         | .error _ => true | .ok _ => false) ""
  -- `[99]`/`[100]`: a bare `!` is the non-specific tag; `!t` is a primary tag with suffix `t`.
  for (input, handle, suffix) in [("! a", "!", ""), ("!t a", "!", "t"), ("!t", "!", "t"),
                                  ("!!str a", "!!", "str"), ("!e!t a", "!e!", "t")] do
    match scanTag (ScannerState.mk' input) with
    | .ok s' =>
      checkM state s!"scanTag/{repr input}: tag {repr handle} {repr suffix}"
        (s'.tokens.back?.map (·.val) == some (.tag handle suffix)) s!"got {repr (s'.tokens.back?.map (·.val))}"
    | .error e => checkM state s!"scanTag/{repr input}: accepted" false s!"{repr e}"

/-! ## Priority 19 — maximal tag leaves: `collectTagSuffixLoop_prod` and the `[97]` lookahead (N1 follow-up)

Every `SCNsTagProperty` arm now ends with `GNot (GChar isTagCharProp)`; the scanner's suffix
loop (`collectTagSuffixLoop`, N1b) delivers it under the premise `inputEnd - offset ≤ fuel`,
exactly as `collectAnchorNameLoop_prod` does for anchors (Priority 18).  Same risk: below the
bound the loop stops MID-suffix and the lookahead is false.  The grid separates
**failed-hypothesis** from **theorem-holds** on empty / singleton / multi-char suffixes and on
every terminator kind; `scanTag`'s landing is checked for all four shorthand/non-specific shapes.
-/

/-- `GNot (GChar isTagCharProp)` at the scanner's landing: end of input or a non-tag char. -/
def gnotTagAtB (s : ScannerState) : Bool :=
  match s.peek? with
  | none => true
  | some c => !L4YAML.CharPredicates.isTagCharBool c

/-- One instance of `collectTagSuffixLoop_prod` from `s` with `fuel`: `(hypothesis held, GNot at the landing)`. -/
def tagSuffixInstance (s : ScannerState) (fuel : Nat) : Bool × Bool :=
  let (_, s') := collectTagSuffixLoop s "" fuel
  (decide (s.inputEnd - s.offset ≤ fuel), gnotTagAtB s')

def testMaximalTagLeaves (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 19: maximal tag leaves (collectTagSuffixLoop_prod, [97] lookahead)"
  -- Fuel grid at `"t.x]"`: the remaining input is 4 bytes; `]` is a flow indicator, not a tag char.
  for fuel in [0, 1, 2, 3, 4, 5] do
    let (hyp, gnot) := tagSuffixInstance (nameState "t.x]") fuel
    checkM state s!"tagSuffix/\"t.x]\" fuel={fuel}: hyp → GNot" (!hyp || gnot) s!"hyp={hyp} gnot={gnot}"
    checkM state s!"tagSuffix/\"t.x]\" fuel={fuel}: bucket = {if hyp then "theorem-holds" else "failed-hypothesis"}"
      (hyp == decide (4 ≤ fuel)) ""
  for fuel in [0, 1, 2] do
    checkM state s!"tagSuffix/\"t.x]\" fuel={fuel}: lookahead refuted without the fuel premise"
      (!(tagSuffixInstance (nameState "t.x]") fuel).2) ""
  -- Suffixes: empty / singleton / multi; terminators: every kind, and end of input.
  for input in ["", "t", "t.x", "t.x]", "t,", "t}", "t ", "t\t", "t\n", "t\r\n", "t{", "t[",
                "t!x", "t'x'", "a:b", "%21", "t#c", "t a", "]", " t", "\uFEFF"] do
    let s := nameState input
    let fuel := s.inputEnd - s.offset
    let (hyp, gnot) := tagSuffixInstance s fuel
    checkM state s!"tagSuffix/{repr input}: holds at fuel = remaining input" (hyp && gnot) s!"gnot={gnot}"
    let (hyp', gnot') := tagSuffixInstance s (fuel + 1)
    checkM state s!"tagSuffix/{repr input}: holds with surplus fuel" (hyp' && gnot') ""
  -- `scanTag`: the token and the lookahead at the landing, on every `[97]` shape.
  for (input, handle, suffix) in [("! a", "!", ""), ("!", "!", ""), ("!t a", "!", "t"), ("!t.x]", "!", "t.x"),
                                  ("!t'x' a", "!", "t'x'"), ("!a:b,", "!", "a:b"), ("!!str a", "!!", "str"),
                                  ("!!", "!!", ""), ("!e!t a", "!e!", "t"), ("!e!t.x}", "!e!", "t.x"),
                                  ("!e! a", "!e!", "")] do
    match scanTag (ScannerState.mk' input) with
    | .ok s' =>
      checkM state s!"scanTag/{repr input}: tag {repr handle} {repr suffix}"
        (s'.tokens.back?.map (·.val) == some (.tag handle suffix)) s!"got {repr (s'.tokens.back?.map (·.val))}"
      checkM state s!"scanTag/{repr input}: GNot (GChar isTagCharProp) at the landing" (gnotTagAtB s') ""
    | .error e => checkM state s!"scanTag/{repr input}: accepted" false s!"{repr e}"
  -- `collectTagHandleLoop_inputEnd`: the handle loop never moves `inputEnd`, for ANY fuel
  -- (below, at, above the remaining input) and ANY accumulated prefix — the lemma has no fuel premise.
  for input in ["abc!x", "abc!", "abc", "", "!", "a.b!", "e!t.x}"] do
    let s := nameState input
    let full := s.inputEnd - s.offset
    for chars in ["", "prefix"] do
      for fuel in [0, 1, 2, full, full + 1] do
        let (_, _, s') := collectTagHandleLoop s chars fuel
        checkM state s!"tagHandleLoop/{repr input} chars={repr chars} fuel={fuel}: inputEnd unchanged"
          (s'.inputEnd == s.inputEnd) s!"got {s'.inputEnd} vs {s.inputEnd}"
        checkM state s!"tagHandleLoop/{repr input} chars={repr chars} fuel={fuel}: offset ≤ inputEnd"
          (s'.offset ≤ s'.inputEnd) ""
  -- `tail_gnot_tag` / `gnot_gchar_of_hmax`: "the head is not a tag char" ↔ `GNot (GChar isTagCharProp)`
  -- at that position: empty tail, every terminator kind, `!` (excluded from `[40]`), and a tag-char head.
  for (tail, expected) in [("", true), (" a", true), ("]", true), (",", true), ("}", true), ("\t", true),
                           ("\n", true), ("\r\n", true), ("[", true), ("{", true), ("\uFEFF", true),
                           ("t", false), (".", false), ("%", false), ("'", false), ("!", true), (":", false)] do
    let s := nameState tail
    checkM state s!"tailGnotTag/{repr tail}: head-not-tag-char ↔ GNot at the tail"
      (gnotTagAtB s == expected) s!"got {gnotTagAtB s}"

/-! ## Priority 20 — `[147]` glued flow value: `flowGluedCollectionValue` refusal grid

`scanValueValidate` now refuses a flow `:` glued to `[`/`{` unless the key is JSON-like
(`[148]`/`[149]`).  The grid separates the refused shapes (plain, empty and explicit yaml keys,
map and sequence context, first entry and after `,`) from the accepted ones (JSON-like keys,
separated values, block context where `a:[1]` is one plain scalar, and the other glued
indicators `" ' & ! *`, which continue the plain scalar per `ns-plain-safe(flow)`).  The fuel
row checks the refusal is `unseparatedValue` at full fuel and only `fuelExhausted` below it.
-/

/-- `(scanner ok, refused as unseparatedValue)` for `scan`. -/
def gluedVerdict (input : String) : Bool × Bool :=
  match scan input with
  | .ok _ => (true, false)
  | .error (.unseparatedValue _ _) => (false, true)
  | .error _ => (false, false)

def testGluedFlowValue (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 20: [147] glued flow value (flowGluedCollectionValue)"
  -- Refused: yaml key × glued collection indicator × map/seq × position.
  for input in ["{a:[1]}", "{a:{b: c}}", "[a:[1]]", "[a:{b: c}]", "{a:[]}", "{a:{}}",
                "{a :[1]}", "{:[1]}", "[:[1]]", "{? a :[1]}", "[? a :[1]]",
                "{x: 1, a:[1]}", "[x, a:[1]]", "{a:[1], x: 1}", "{\n  a:[1]}"] do
    checkM state s!"glued/refused {input.quote}" (gluedVerdict input == (false, true))
      s!"verdict={gluedVerdict input}"
  -- Accepted: JSON-like key adjacent value ([148]/[149]).
  for input in ["{\"a\":[1]}", "{'a':{b: c}}", "{[a]:[1]}", "{{a: b}:[1]}", "[\"a\":[1]]",
                "{x: 1, \"a\":[1]}"] do
    checkM state s!"glued/json-key {input.quote}" (gluedVerdict input == (true, false))
      s!"verdict={gluedVerdict input}"
  -- Accepted: separated value (a break is `[80] s-separate-lines` in flow), block context, and
  -- the non-collection glued indicators.
  for input in ["{a: [1]}", "{a:\t[1]}", "{a:\n[1]}", "a: [1]", "a:[1]", "a:{b}", "{a:b}", "{a:\"x\"}",
                "{a:'x'}", "{a:&x b}", "{a:!t b}", "{a:*x}"] do
    checkM state s!"glued/control {input.quote}" (gluedVerdict input == (true, false))
      s!"verdict={gluedVerdict input}"
  -- Fuel row at `{a:[1]}`: 5 tokens are needed to reach the refusal.
  for fuel in [0, 1, 2, 3, 4, 5, 6, 8, 16] do
    let r := scanLoop (ScannerState.mk' "{a:[1]}") fuel
    let kind := match r with
      | .error (.fuelExhausted _ _) => "fuelExhausted"
      | .error (.unseparatedValue _ _) => "unseparatedValue"
      | .error _ => "otherError"
      | .ok _ => "ok"
    checkM state s!"glued/fuel={fuel}: refusal kind" (kind == "fuelExhausted" || kind == "unseparatedValue")
      s!"kind={kind}"
    checkM state s!"glued/fuel={fuel}: monotone" (fuel < 3 || kind == "unseparatedValue") s!"kind={kind}"

/-! ## Priority 21 — glued-`:` scanner lemmas: `flowGluedCollectionValue_false_of_*` and `isValueCandidate_glued_jsonKey`

Rule-2 instantiations of the five scanner lemmas behind the `[147]`/`[149]` split, taken on the
scanner's own reachable states: every state at which `scanNextToken` / `scanNextTokenIx` pauses
with `:` under the cursor while scanning the grid input.  Each (lemma, state) row is classified
failed-hypothesis / theorem-holds / theorem-refuted; a refutation fails the suite, and the tally
of each class is pinned so a hypothesis that silently fails on every row is caught (§7), legacy
and indexed are compared row by row, and `{a:b}` pins that the scanner never pauses at a `:` the
plain scalar absorbed.
-/

open L4YAML.CharPredicates L4YAML.Proofs.FlowAdjacency L4YAML.Proofs.FlowAdjacencyIx
  L4YAML.Scanner.Indexed L4YAML.Scanner.Indexed.ScannerStateIx

/-- Rule-2 classification of one (lemma, state) row. -/
inductive Rule2Row where
  | failedHyp | holds | refuted
  deriving BEq, Repr, Inhabited

def Rule2Row.of (hyp concl : Bool) : Rule2Row :=
  if !hyp then .failedHyp else if concl then .holds else .refuted

/-- Every legacy state at which the scanner pauses with `:` under the cursor while scanning
    `input` (the initial state included), in scan order; scanning stops at the first error. -/
def colonStates (input : String) (fuel : Nat := 64) : List ScannerState := Id.run do
  let mut s := ScannerState.mk' input
  let mut acc : List ScannerState := if s.peek? == some ':' then [s] else []
  for _ in [:fuel] do
    match scanNextToken s with
    | .error _ => return acc
    | .ok none => return acc
    | .ok (some s') =>
      s := s'
      if s.peek? == some ':' then acc := acc ++ [s]
  return acc

/-- The indexed twin of `colonStates`. -/
def colonStatesIx (input : String) (fuel : Nat := 64) : List (ScannerStateIx input) := Id.run do
  let mut s := ScannerStateIx.mk' input
  let mut acc : List (ScannerStateIx input) := if s.peek? == some ':' then [s] else []
  for _ in [:fuel] do
    match scanNextTokenIx s with
    | .error _ => return acc
    | .ok none => return acc
    | .ok (some s') =>
      s := s'
      if s.peek? == some ':' then acc := acc ++ [s]
  return acc

/-- `flowGluedCollectionValue_false_of_peekAt_blank` at `s`. -/
def rowGluedBlank (s : ScannerState) : Rule2Row :=
  .of (s.peekAt? 1 == some ' ') (flowGluedCollectionValue s == false)

/-- `flowGluedCollectionValueIx_false_of_peekAt_blank` at `s`. -/
def rowGluedBlankIx {input : String} (s : ScannerStateIx input) : Rule2Row :=
  .of (s.peekAt? 1 == some ' ') (flowGluedCollectionValueIx s == false)

/-- `flowGluedCollectionValue_false_of_corr_colon_blank` at `s`: the decidable shadow of its
    `ScannerSurfCorr s ⟨':' :: ' ' :: rest', s.col⟩` premise on ASCII input is "the characters
    from the cursor start `: `". -/
def rowGluedCorr (s : ScannerState) : Rule2Row :=
  let hyp := match s.input.toList.drop s.offset with
    | ':' :: ' ' :: _ => true
    | _ => false
  .of hyp (flowGluedCollectionValue s == false)

/-- `isValueCandidate_glued_jsonKey` at `s`. -/
def rowJsonKey (s : ScannerState) : Rule2Row :=
  let hyp := s.inFlow
    && (match s.peekAt? 1 with
        | some n => !(isBlankBool n || isFlowIndicatorBool n)
        | none => false)
    && isValueCandidate s
  let concl := s.simpleKey.possible
    && (match flowKeyToken s with
        | some tok => isJsonNodeToken tok.val
        | none => false)
  .of hyp concl

/-- `isValueCandidateIx_glued_jsonKey` at `s`. -/
def rowJsonKeyIx {input : String} (s : ScannerStateIx input) : Rule2Row :=
  let hyp := s.inFlow
    && (match s.peekAt? 1 with
        | some n => !(isBlankBool n || isFlowIndicatorBool n)
        | none => false)
    && isValueCandidateIx s
  let concl := s.simpleKey.possible
    && (match flowKeyTokenIx s with
        | some t => isJsonNodeTokenIx t.token
        | none => false)
  .of hyp concl

/-- The grid: empty / bare `:` / blank, tab, break after `:` / glued `[` `{` after a plain key
    (the `[147]` refusal) and after each JSON-like key kind (`[149]`) / glued plain, quoted,
    alias, anchored, tagged values after a JSON key / first, after-`,`, before-`,`, nested
    positions / block context.  `{a:b}` is the absorbed-`:` control (no pause). -/
def gluedScannerGrid : List String :=
  ["", ":", ": ", ":[", "{:[1]}", "[: a]",
   "{a: [1]}", "{a: b}", "[a: [1]]", "{\"a\": [1]}", "{x: 1, a: [1]}", "{a: [1], x: 1}",
   "a: [1]", "a:\n  [1]",
   "{a:[1]}", "{a:{b: c}}", "[a:[1]]", "{x: 1, a:[1]}", "{a:[1], x: 1}", "{a :[1]}",
   "{\"a\":[1]}", "{'a':{b: c}}", "{[a]:[1]}", "{{a: b}:[1]}", "[\"a\":[1]]", "{x: 1, \"a\":[1]}",
   "{\"a\":b}", "{'a':b}", "{[a]:b}", "{{a: b}:c}", "[\"a\":b]", "{x: 1, \"a\":b}", "{\"a\":b, x: 1}",
   "{\"a\":\"x\"}", "{\"a\":'x'}", "{\"a\":*x}", "{\"a\":&x b}", "{\"a\":!t b}",
   "{o: {\"a\":b}}", "{\"a\":{\"b\":c}}", "[[\"a\":b]]",
   "{a:\t[1]}", "{a:\n[1]}",
   "\"a\":b", "\"a\":[1]", "a:[1]", "? a\n:[1]", "{a:b}"]

def Rule2Row.label : Rule2Row → String
  | .failedHyp => "failed-hypothesis"
  | .holds => "theorem-holds"
  | .refuted => "theorem-refuted"

def tallyRows (rows : List Rule2Row) : String :=
  s!"holds={(rows.filter (· == .holds)).length} failedHyp={(rows.filter (· == .failedHyp)).length} refuted={(rows.filter (· == .refuted)).length}"

def testGluedScannerLemmas (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 21: glued-':' scanner lemmas (flowGluedCollectionValue / isValueCandidate_glued_jsonKey)"
  let mut blank : List Rule2Row := []
  let mut corr : List Rule2Row := []
  let mut json : List Rule2Row := []
  let mut states := 0
  for input in gluedScannerGrid do
    let ss := colonStates input
    let ts := colonStatesIx input
    checkM state s!"p21/{input.quote}: legacy and indexed pause at the same number of ':'"
      (ss.length == ts.length) s!"legacy={ss.length} indexed={ts.length}"
    states := states + ss.length
    for (s, i) in ss.zipIdx do
      let rb := rowGluedBlank s
      let rc := rowGluedCorr s
      let rj := rowJsonKey s
      blank := blank ++ [rb]; corr := corr ++ [rc]; json := json ++ [rj]
      checkM state s!"p21/{input.quote}#{i}: flowGluedCollectionValue_false_of_peekAt_blank not refuted"
        (rb != .refuted) rb.label
      checkM state s!"p21/{input.quote}#{i}: flowGluedCollectionValue_false_of_corr_colon_blank not refuted"
        (rc != .refuted) rc.label
      checkM state s!"p21/{input.quote}#{i}: isValueCandidate_glued_jsonKey not refuted"
        (rj != .refuted) rj.label
      match ts[i]? with
      | some t =>
        checkM state s!"p21/{input.quote}#{i}: Ix twin of *_false_of_peekAt_blank agrees"
          (rowGluedBlankIx t == rb) s!"legacy={rb.label} indexed={(rowGluedBlankIx t).label}"
        checkM state s!"p21/{input.quote}#{i}: Ix twin of isValueCandidate_glued_jsonKey agrees"
          (rowJsonKeyIx t == rj) s!"legacy={rj.label} indexed={(rowJsonKeyIx t).label}"
      | none => pure ()
  checkM state "p21: {a:b} never pauses at the absorbed ':'" ((colonStates "{a:b}").length == 0)
    s!"pauses={(colonStates "{a:b}").length}"
  -- The grid is not vacuous for any lemma: both classes are populated, and the tallies are pinned.
  checkM state "p21: tally *_false_of_peekAt_blank" (tallyRows blank == "holds=19 failedHyp=36 refuted=0")
    (tallyRows blank)
  checkM state "p21: tally *_false_of_corr_colon_blank" (tallyRows corr == "holds=19 failedHyp=36 refuted=0")
    (tallyRows corr)
  checkM state "p21: tally isValueCandidate_glued_jsonKey" (tallyRows json == "holds=15 failedHyp=40 refuted=0")
    (tallyRows json)
  checkM state "p21: colon states over the grid" (states == 55) s!"states={states}"
  -- The failed-hypothesis rows are not silent: at a glued `[`/`{` the predicate the lemmas bound
  -- is TRUE after a plain key (the `[147]` refusal fires) and FALSE after a JSON-like key.
  for input in ["{a:[1]}", "{a:{b: c}}", "[a:[1]]", "{x: 1, a:[1]}", "{a:[1], x: 1}", "{:[1]}"] do
    let v := (colonStates input).getLast?.map flowGluedCollectionValue
    checkM state s!"p21/{input.quote}: glued predicate fires after a plain key" (v == some true) s!"v={v}"
  for input in ["{\"a\":[1]}", "{'a':{b: c}}", "{[a]:[1]}", "{{a: b}:[1]}", "[\"a\":[1]]"] do
    let v := ((colonStates input).getLast?).map flowGluedCollectionValue
    checkM state s!"p21/{input.quote}: glued predicate silent after a JSON key" (v == some false) s!"v={v}"

/-! ## Priority 22 — the widened stale hook and the column-0 landing fact (items 348–349, row 12)

Item 348 made `closeStaleExplicitKey` close EVERY marked `pendingKeys` level the
cursor lands at or left of (`PendingKeys.closeStale`), and item 349 narrowed its
`-`/`:` exemption to the characters the dispatcher treats as indicators
(`PendingKeys.indicatorAt c next`: `-`/`:` followed by a blank or EOF).  The
landing fact `preprocess_col0_dead` is what `content_dispatch_routed` spends at
its `k = 0` value-line fields, so its hypotheses are instantiated here on real
scanner walks, and each helper lemma on a grid of synthetic stacks.

**Risk:** the slot formula (`closeStale_getElem?`), size preservation and the
marked-before property; `innermost_closeStale_col0` needs `0 ≤ m` on every marked
slot (a `-1` slot refutes the unguarded statement); the gate must keep `-`/`:`
only as indicators (`?⏎-x: 1` refuted the raw-character exemption); and the
landing fact is FALSE when the landing character is an indicator (`?⏎- a`).
-/

/-- Decidable `SlotsOk`-shaped check: `pendingKeys` matches `indents` in size and every
    marked slot sits on a column `≥ 0`. -/
def slotsOkB (s : ScannerState) : Bool :=
  s.pendingKeys.size == s.indents.size &&
    (List.range s.pendingKeys.size).all fun i =>
      match s.pendingKeys[i]? with
      | some (some _) => (s.indents[i]?.map (·.column)).any (fun m => 0 ≤ m)
      | _ => true

/-- Walk `scanNextToken` from `mk'`; at each step where the pre-state is `Sound`, outside flow,
    the preprocessed cursor sits at column 0 and the landing character is not an indicator,
    require the register dead.  Returns `(steps, landings checked, refutations)`. -/
def walkCol0Dead (input : String) : Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut steps := 0
  let mut landings := 0
  let mut refuted := 0
  let mut fuel := input.length + 8
  while fuel > 0 do
    fuel := fuel - 1
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      if soundB s && !s.inFlow && sp.col == 0
          && !(PendingKeys.indicatorAt c (sp.peekAt? 1)) then
        landings := landings + 1
        if sp.explicitKeyLine != none then refuted := refuted + 1
    | _ => pure ()
    match scanNextToken s with
    | .ok (some s') => steps := steps + 1; s := s'
    | _ => fuel := 0
  return (steps, landings, refuted)

def testColZeroLanding (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 22: widened stale hook and the column-0 landing fact (items 348–349)"
  -- `indicatorAt`: `-`/`:` are indicators only before a blank or at EOF.
  let indRows : List (Char × Option Char × Bool) :=
    [('-', some ' ', true), ('-', none, true), ('-', some 'x', false), ('-', some '\n', true),
     (':', some ' ', true), (':', none, true), (':', some 'x', false),
     ('a', some ' ', false), ('a', none, false), ('?', some ' ', false)]
  for (c, next, expected) in indRows do
    checkM state s!"indicatorAt/{repr c} before {repr next}"
      (PendingKeys.indicatorAt c next == expected) ""
  -- `staleGate`: content at or left of the level closes; `-` closes only strictly left; `:`
  -- never at its own column; a non-indicator `-`/`:` closes like content; right of the level
  -- nothing closes (`staleGate_false_le`: gate false ⇒ m ≤ col).
  let gateRows : List (Int × Int × Char × Option Char × Bool) :=
    [(0, 0, 'a', some ' ', true), (0, 2, 'a', some ' ', true), (2, 0, 'a', some ' ', false),
     (2, 2, '-', some ' ', false), (0, 2, '-', some ' ', true), (2, 2, '-', some 'x', true),
     (2, 2, ':', some ' ', false), (0, 2, ':', some ' ', true), (2, 2, ':', some 'x', true),
     (0, 0, '-', none, false), (0, 0, ':', none, false), (3, 2, '-', some ' ', false)]
  for (col, m, c, next, expected) in gateRows do
    checkM state s!"staleGate/col {col} level {m} {repr c} before {repr next}"
      (PendingKeys.staleGate col m c next == expected) ""
    if !(PendingKeys.staleGate col m c next) then
      checkM state s!"staleGate_false_le/col {col} level {m} {repr c}" (m ≤ col) ""
  -- `closeStale` grid: empty, singleton, two and three levels; cursor at 0 and 2; every
  -- character class and lookahead.  Size is preserved; every slot still marked was marked
  -- before; at column 0 with a non-indicator the innermost marked slot is gone whenever every
  -- marked level is `≥ 0` (`innermost_closeStale_col0`), and a `-1` level refutes it.
  let stacks : List (Array Int × Array (Option Nat)) :=
    [(#[], #[]), (#[-1], #[none]), (#[0], #[some 0]), (#[-1, 0], #[none, some 0]),
     (#[-1, 0, 2], #[none, some 0, some 1]), (#[-1, 0, 2], #[none, none, some 1]),
     (#[-1, 0, 2], #[some 7, none, none]), (#[-1, 2, 4], #[none, some 0, some 1])]
  let chars : List (Char × Option Char) :=
    [('a', some ' '), ('-', some ' '), ('-', some 'x'), ('-', none), (':', some ' '), (':', some 'x')]
  for (cols, pks) in stacks do
    for col in [(0 : Int), 2] do
      for (c, next) in chars do
        let out := PendingKeys.closeStale cols pks col c next
        let tag := s!"closeStale/{repr cols} {repr pks} col {col} {repr c} {repr next}"
        checkM state s!"{tag}: size" (out.size == pks.size) ""
        checkM state s!"{tag}: marked-before"
          ((List.range out.size).all fun i =>
            match out[i]? with
            | some (some l) => pks[i]? == some (some l)
            | _ => true) ""
        checkM state s!"{tag}: formula"
          ((List.range out.size).all fun i =>
            out[i]? == some (match cols[i]? with
              | some m => if PendingKeys.staleGate col m c next then none else pks[i]?.getD none
              | none => pks[i]?.getD none)) ""
        let allNonneg := (List.range pks.size).all fun i =>
          match pks[i]? with
          | some (some _) => (cols[i]?.map (fun m => decide (0 ≤ m))).getD false
          | _ => true
        if col == 0 && !(PendingKeys.indicatorAt c next) then
          if allNonneg then
            checkM state s!"{tag}: innermost dead (innermost_closeStale_col0)"
              ((PendingKeys.innermost cols out).1 == none) ""
          else
            checkM state s!"{tag}: `-1` level survives (premise failure, refutes the unguarded form)"
              ((PendingKeys.innermost cols out).1 != none) ""
  -- `closeStaleAt_slots` / `SlotsWitness.closeStale`: the state-level hook keeps `SlotsOk`
  -- and only ever un-marks (the witness is per marked slot, so un-marking cannot break it).
  for input in ["?\n  ? a\nc", "? ? a\n  : b\nc", "?\n-x"] do
    let s := { staleStateAt input (input.length - 1) 2 0 (some 0) 2 0 with
      indents := #[{ column := -1, isSequence := false }, { column := 0, isSequence := false },
                   { column := 2, isSequence := false }],
      pendingKeys := #[none, some 0, some 1] }
    for c in ['a', '-', ':'] do
      let s' := s.closeStaleAt c
      checkM state s!"closeStaleAt/{repr input} {repr c}: SlotsOk kept" (slotsOkB s') ""
      checkM state s!"closeStaleAt/{repr input} {repr c}: marked-before"
        ((List.range s'.pendingKeys.size).all fun i =>
          match s'.pendingKeys[i]? with
          | some (some l) => s.pendingKeys[i]? == some (some l)
          | _ => true) ""
  -- `reg_col_nonneg`: on every walked state outside flow with a live register the column is
  -- `≥ 0` (the seed `mk'` has `explicitKeyCol = -1` but no register).
  for input in ["? a\n: b", "?\n  ? a\nc: 1", "- ? a\n  : b", "? ? a\n  : b\nc: 1"] do
    let mut s := ScannerState.mk' input
    let mut ok := true
    let mut fuel := input.length + 8
    while fuel > 0 do
      fuel := fuel - 1
      if s.flowLevel == 0 && s.explicitKeyLine != none && soundB s && s.explicitKeyCol < 0 then
        ok := false
      match scanNextToken s with
      | .ok (some s') => s := s'
      | _ => fuel := 0
    checkM state s!"reg_col_nonneg/{repr input}" ok ""
  -- `hook_col0_dead` (synthetic): a column-0 cursor under a non-indicator kills the register
  -- whatever the marked levels; the indicator rows keep it (hypothesis failure, not a bug).
  for (c, dead) in [('c', true), ('-', false), (':', false)] do
    let input := s!"?\n  ? a\n{c} x"
    let s := { staleStateAt input 8 2 0 (some 1) 2 0 with
      indents := #[{ column := -1, isSequence := false }, { column := 0, isSequence := false },
                   { column := 2, isSequence := false }],
      pendingKeys := #[none, some 0, some 1] }
    checkM state s!"hook_col0_dead/{repr c} at column 0: register {if dead then "dead" else "live"}"
      (((closeStaleExplicitKey s).explicitKeyLine == none) == dead) ""
  -- `preprocess_col0_dead` on real walks: every column-0 non-indicator landing finds the register
  -- dead (theorem-holds), and the probe set includes landings the statement must NOT claim.
  for (input, minLandings) in
      [("?\n  ? a\nc: 1", 1), ("?\n  ? a\n  ? b\nc: 1", 1), ("? ? a\n  : b\nc: 1", 1),
       ("?\n-x: 1", 1), ("?\n  ? a\n-x: 1", 1), ("?\n:x", 1), ("?\n  a: 1\nb: 2", 1),
       ("? a\n---", 1), ("?\n- a", 0), ("?\n  ? a\n: v", 0), ("?\n  b: c\n  d: e\n: v", 0)] do
    let (steps, landings, refuted) := walkCol0Dead input
    checkM state s!"preprocess_col0_dead/{repr input}: walked" (steps > 0) s!"{steps} steps"
    checkM state s!"preprocess_col0_dead/{repr input}: {landings} column-0 landing(s) checked"
      (landings ≥ minLandings) s!"got {landings}"
    checkM state s!"preprocess_col0_dead/{repr input}: no refutation" (refuted == 0)
      s!"{refuted} live register(s) at a column-0 content landing"
  -- The indicator landings are the rows the statement excludes: the first column-0 landing
  -- of `?⏎- a` and `?⏎  ? a⏎: v` is an indicator and the register is still live there.
  for input in ["?\n- a", "?\n  ? a\n: v"] do
    let mut s := ScannerState.mk' input
    let mut found : Option (ScannerState × Char) := none
    let mut fuel := input.length + 8
    while fuel > 0 do
      fuel := fuel - 1
      match scanNextToken_preprocess s with
      | .ok (some (sp, c)) =>
        if sp.col == 0 && sp.offset > 0 && found.isNone then found := some (sp, c)
      | _ => pure ()
      match scanNextToken s with
      | .ok (some s') => s := s'
      | _ => fuel := 0
    match found with
    | some (sp, c) =>
      checkM state s!"preprocess_col0_dead/{repr input}: indicator landing (hypothesis fails)"
        (PendingKeys.indicatorAt c (sp.peekAt? 1) && sp.explicitKeyLine == some 0)
        s!"c = {repr c}, register {repr sp.explicitKeyLine}"
    | none => checkM state s!"preprocess_col0_dead/{repr input}: column-0 landing found" false ""
  -- `indicatorAt_false_of_dispatch_none`: a declined block dispatch means no indicator, and
  -- the indicator rows are exactly the ones the dispatcher takes.
  for (input, declined) in [("-x", true), (":x", true), ("a", true), ("- a", false),
                            (": a", false), ("-", false), (":", false)] do
    let s := ScannerState.mk' input
    match s.peek? with
    | some c =>
      let none? := match scanNextToken_dispatchBlockIndicators s c with
        | .ok none => true | _ => false
      checkM state s!"dispatch_none/{repr input}: declined" (none? == declined) ""
      if none? then
        checkM state s!"dispatch_none/{repr input}: no indicator"
          (PendingKeys.indicatorAt c (s.peekAt? 1) == false) ""
    | none => checkM state s!"dispatch_none/{repr input}: peek" false ""
  -- `closeStaleExplicitKey_peekAt?` (review of #87): neither hook branch moves the lookahead —
  -- the resetting branch (live `?` at column 0 over `-x`/`a`/`:x`) and the identity branch
  -- (`- `, `: `, a bare `-` are indicators), at offsets 0, 1, 2 and past the end, both pipelines.
  for (input, resets) in [("-x: 1", true), ("a", true), (":x", true), ("- a", false),
                          (": a", false), ("-", false)] do
    let s := staleStateAt input 0 0 0 (some 0) 0 0
    let s' := closeStaleExplicitKey s
    checkM state s!"peekAt/{repr input}: branch" ((s'.explicitKeyLine == none) == resets)
      s!"register {repr s'.explicitKeyLine}"
    let t := staleStateIxAt input 0 (some 0) 0 0
    let t' := t.closeStaleExplicitKeyIx
    for n in [0, 1, 2, 100] do
      checkM state s!"peekAt/{repr input}/{n}: legacy lookahead preserved"
        (s'.peekAt? n == s.peekAt? n) s!"{repr (s'.peekAt? n)} vs {repr (s.peekAt? n)}"
      checkM state s!"peekAt/{repr input}/{n}: indexed lookahead preserved"
        (t'.peekAt? n == t.peekAt? n) s!"{repr (t'.peekAt? n)} vs {repr (t.peekAt? n)}"

/-! ## Priority 23 — `NotQuestionPark` and the `:` producers' payment (item 350, row 12)

Item 350 gave `PendingNode.pendingMapValue`'s two `?`-entry faces (`h_expl`,
`h_explUp`) the alternative `NotQuestionPark sc` — "the last real token is not
`.key`" — in place of `PackAlt sc`, because at a `:` park inside an open `?` the
register is LIVE (`? a: b⏎: c`) and the field was unsatisfiable under the flip.
Every `:` producer pays it from the dispatch (`scanValue_notQuestion`,
`dispatchBlock_colon_notQuestion`, via `notQuestion_push_top`), and the `?`
producer (`question_open_map`) cannot: its tail IS `.key`.  Consumers spend the
alternative as the EMPTY value-line chain (`ns := []`), so nothing below reads it.

**Risk:** `notQuestion_push_top` needs BOTH hypotheses — pushing `.key` refutes
the conclusion, and pushing a `.placeholder` onto a `.key` top keeps the `?`
tail (`prevRealIdx?` walks past placeholders); the predicate is vacuous on an
empty history; and on real walks a `?` dispatch must leave the predicate FALSE
(otherwise the `?` producer could have paid `inr` and the `inl` payment was
unnecessary).
-/

/-- Decidable mirror of `NotQuestionPark` on a token history. -/
def notQuestionParkB (ts : Array (Positioned YamlToken)) : Bool :=
  match prevRealIdx? ts ts.size with
  | some i => (match ts[i]!.val with | .key => false | _ => true)
  | none => true

def testNotQuestionPark (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 23: NotQuestionPark and the `:` producers (item 350)"
  -- `notQuestion_push_top`, hypothesis level: a non-placeholder, non-key push makes the
  -- predicate true on every history; a `.key` push refutes it (`hk`); a `.placeholder` push
  -- onto a `.key` top leaves it false (`hp`).
  match scanNextToken (ScannerState.mk' "? a") with
  | .ok (some s1) =>
    match s1.tokens[0]? with
    | some p =>
      let mk (t : YamlToken) : Positioned YamlToken := { p with val := t }
      let bases : List (String × Array (Positioned YamlToken)) :=
        [("empty", #[]), ("key", #[mk .key]), ("value", #[mk .value]),
         ("key+placeholder", #[mk .key, mk .placeholder]),
         ("value+placeholder", #[mk .value, mk .placeholder]),
         ("key+key", #[mk .key, mk .key])]
      -- Every `YamlToken` constructor but the two the lemma excludes (`hp`, `hk`), the
      -- parameterised ones with a representative payload and `scalar` in all five styles.
      let kinds : List (String × YamlToken) :=
        [("streamStart", .streamStart), ("streamEnd", .streamEnd),
         ("versionDirective", .versionDirective 1 2), ("tagDirective", .tagDirective "!" "!foo"),
         ("documentStart", .documentStart), ("documentEnd", .documentEnd),
         ("blockSequenceStart", .blockSequenceStart), ("blockMappingStart", .blockMappingStart),
         ("blockEnd", .blockEnd), ("blockEntry", .blockEntry), ("value", .value),
         ("flowSequenceStart", .flowSequenceStart), ("flowSequenceEnd", .flowSequenceEnd),
         ("flowMappingStart", .flowMappingStart), ("flowMappingEnd", .flowMappingEnd),
         ("flowEntry", .flowEntry), ("anchor", .anchor "a"), ("alias", .alias "a"),
         ("tag", .tag "!" "x"), ("scalar/plain", .scalar "x" .plain),
         ("scalar/singleQuoted", .scalar "x" .singleQuoted),
         ("scalar/doubleQuoted", .scalar "x" .doubleQuoted),
         ("scalar/literal", .scalar "x" .literal), ("scalar/folded", .scalar "x" .folded),
         ("comment", .comment "c")]
      for (name, ts) in bases do
        for (kind, t) in kinds do
          checkM state s!"push_top/{name}/{kind}" (notQuestionParkB (ts.push (mk t))) ""
        checkM state s!"push_top/{name}/key refutes (hk)" (!notQuestionParkB (ts.push (mk .key))) ""
      checkM state "push_top/key+placeholder+placeholder: still a `?` tail (hp)"
        (!notQuestionParkB (#[mk .key, mk .placeholder].push (mk .placeholder))) ""
      checkM state "push_top/value+placeholder+placeholder: still a value tail"
        (notQuestionParkB (#[mk .value, mk .placeholder].push (mk .placeholder))) ""
      checkM state "NotQuestionPark/empty history: vacuous" (notQuestionParkB #[]) ""
      checkM state "NotQuestionPark/placeholder-only history: vacuous"
        (notQuestionParkB #[mk .placeholder]) ""
    | none => checkM state "push_top/seed token" false ""
  | _ => checkM state "push_top/seed step" false ""
  -- `scanValue_notQuestion` / `dispatchBlock_colon_notQuestion` on real walks: every `:` the
  -- block dispatcher takes leaves a non-`?` tail, and every `?` it takes leaves a `?` tail
  -- (`question_open_map` pays the face by `ns := []`, not by `NotQuestionPark`).
  for input in ["? a: b\n: c", "? ? a\n  : b\n: c", "a: 1", "- a: b", "? a\n: b",
                "? &p a: 1\n: c", "- ? a\n- ? b", ": a", "? [1]: b\n: - w", "?\n  ?\n    ?\n: w"] do
    let mut s := ScannerState.mk' input
    let mut colons := 0
    let mut questions := 0
    let mut bad := 0
    let mut fuel := input.length + 8
    while fuel > 0 do
      fuel := fuel - 1
      match scanNextToken_preprocess s with
      | .ok (some (sp, c)) =>
        if c == ':' || c == '?' then
          match scanNextToken_dispatchBlockIndicators sp c with
          | .ok (some s') =>
            if c == ':' then
              colons := colons + 1
              if !notQuestionParkB s'.tokens then bad := bad + 1
            else
              questions := questions + 1
              if notQuestionParkB s'.tokens then bad := bad + 1
          | _ => pure ()
      | _ => pure ()
      match scanNextToken s with
      | .ok (some s') => s := s'
      | _ => fuel := 0
    checkM state s!"dispatch/{repr input}: `:` tails are not `?`, `?` tails are" (bad == 0)
      s!"colons {colons} questions {questions} bad {bad}"
    checkM state s!"dispatch/{repr input}: an indicator was dispatched" (colons + questions > 0) ""

/-! ## Priority 24 — the marked-column domain and its transport (item 355, row 12)

Item 355 narrows five value-line faces to `∃ ns, MarkedColsIn sc ns ∧ …`: every marked
`pendingKeys` column is in `ns`.  The domain is carried across every scanner writer but the
`?` (`MarkedColsIn.pop`/`closeStale`/`transport`, `preprocess_markedCols`,
`dispatchContent_markedCols`, `MarkedColsIn.step_content`) — marks only shrink off the `?`
step — and `MarkedColsIn.pop` claims this WITHOUT the `pendingKeys`/`indents` lockstep.

**Risk:** a writer that re-marks a slot (the transport would be false); the `?` adding a
mark at a column other than the top level; a pop on non-lockstep arrays moving a mark to
another column.  Instantiated on real scans (fuel 0/1/2, nested `?`, compact `? ?`, flow,
documents) and on a synthetic non-lockstep grid.
-/

/-- The columns of the marked slots (the decidable reading of `MarkedColsIn`'s domain). -/
def markedColsOf (pks : Array (Option Nat)) (cols : Array Int) : List Nat :=
  (List.range pks.size).filterMap fun i =>
    match pks[i]? with
    | some (some _) => (cols[i]?).map Int.toNat
    | _ => none

/-- Walk `scanNextToken` from `mk'`: at every step the new marked columns must be a subset of
    the old ones, or — when a mark was added — of the old ones plus the top level's column.
    Returns `(steps, steps that added a mark, violations)`. -/
def walkMarkedShrink (input : String) : Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut fuel := 64
  let mut steps := 0
  let mut grown := 0
  let mut bad := 0
  while fuel > 0 do
    fuel := fuel - 1
    match scanNextToken s with
    | .ok (some s') =>
      let before := markedColsOf s.pendingKeys s.indentColumns
      let after := markedColsOf s'.pendingKeys s'.indentColumns
      let top := (s'.indentColumns[s'.indents.size - 1]?).map Int.toNat
      let allowed := match top with | some c => c :: before | none => before
      if after.length > before.length then grown := grown + 1
      if !(after.all fun c => allowed.contains c) then bad := bad + 1
      steps := steps + 1; s := s'
    | _ => fuel := 0
  return (steps, grown, bad)

def testMarkedColsDomain (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 24: the marked-column domain and its transport (item 355)"
  -- real scans: `(input, expected `?` marks added)`
  let walks : List (String × Nat) :=
    [("", 0), ("a", 0), ("a: 1\n", 0), ("? a\n", 1), ("? a\nb: 1\n", 1),
     ("?\n  b: c\n  d: e\n: v\n", 1), ("?\n  ? a\n  b\n: v\n", 2),
     ("? ? a\n  : b\nc: 1\n", 2), ("- ? a\n- ? b\n", 2), ("?\n- a\n", 1),
     ("? [a, b]: 1\n", 1), ("{a: 1}\n", 0), ("---\n? a\n...\n", 1), ("?\n  ? a\n  ? b\nc: 1\n", 2)]
  -- (`? b` re-marks the column-2 level the landing just closed: same columns before and after,
  -- so it is not growth — the transport rows still hold.)
  for (input, expectedGrown) in walks do
    let (steps, grown, bad) := walkMarkedShrink input
    checkM state s!"markedShrink/{repr input}: marks only shrink off the `?` step" (bad == 0)
      s!"steps {steps} grown {grown} bad {bad}"
    checkM state s!"markedShrink/{repr input}: `?` marks added" (grown == expectedGrown)
      s!"grown {grown} expected {expectedGrown}"
  -- `MarkedColsIn.pop` without lockstep: popping both arrays never moves a mark to another
  -- column — the surviving marked columns are a subset of the old ones.
  let grid : List (Array Int × Array (Option Nat)) :=
    [(#[], #[]), (#[-1], #[none]), (#[-1, 0], #[none, some 0]), (#[-1, 0, 2], #[none, some 0, some 1]),
     (#[-1, 0], #[none, some 0, some 1]), (#[-1, 0, 2], #[none, some 0]), (#[-1], #[some 3, some 4]),
     (#[-1, 0, 2, 4], #[none, some 0, none, some 2])]
  for (cols, pks) in grid do
    let before := markedColsOf pks cols
    let after := markedColsOf pks.pop cols.pop
    checkM state s!"pop/{repr cols} {repr pks}: marked columns shrink" (after.all fun c => before.contains c)
      s!"before {before} after {after}"

/-! ## Priority 25 — the `[66]` col-0 parks: `NextIsSep`, the comment gate and the JSON-key carry (B3)

`s-separate-in-line` is empty only at column 0 now, so every park at column > 0 must show the
scanner left a real separator behind it.  The rows instantiate the three scanner facts the
StreamAccum frames spend, on the scanner's own reachable states (every state after a
`scanNextToken` step on the grid input): `nextIsSep_of_scanValue` / `_scanKey` /
`_scanBlockEntry` / `_propertyFollowerOk` (a block `:` `?` `-` `&x` `!t` is followed by a
blank, a flow indicator or eof), `content_park_gate` (a content token parked before `#` at
column > 0 has a white run behind it — the `[66]` separator), and `jsonKeyBefore_scanValue` /
`jsonKeyOfLast_of_glued` (the `:` write preserves the key's JSON-ness, and a glued follower
after a flow `:` means the key was JSON-like).  A refutation fails the suite; each class's
tally is pinned so a hypothesis that fails on every row is caught (§7).
-/

/-- Decidable shadow of `NextIsSep`. -/
def nextIsSepB (s : ScannerState) : Bool :=
  match s.peek? with
  | none => true
  | some ch => isBlankBool ch || ch == ',' || ch == ']' || ch == '}'

/-- Decidable shadow of `CommentOk`. -/
def commentOkB (s : ScannerState) : Bool :=
  s.col == 0 || (match s.peekBack? with
    | none => true
    | some c => isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF')

/-- The last real (non-placeholder) token of `s`. -/
def lastReal (s : ScannerState) : Option YamlToken :=
  (s.tokens.toList.reverse.find? (fun p => p.val != .placeholder)).map (·.val)

/-- Every `(before, after)` pair of a successful legacy `scanNextToken` step on `input`, in scan
    order; scanning stops at the first error. -/
def stepPairs (input : String) (fuel : Nat := 64) : List (ScannerState × ScannerState) := Id.run do
  let mut s := ScannerState.mk' input
  let mut acc : List (ScannerState × ScannerState) := []
  for _ in [:fuel] do
    match scanNextToken s with
    | .error _ => return acc
    | .ok none => return acc
    | .ok (some s') =>
      acc := acc ++ [(s, s')]
      s := s'
  return acc

def isContentTok : YamlToken → Bool
  | .scalar _ _ | .alias _ | .flowSequenceEnd | .flowMappingEnd => true
  | _ => false

/-- `nextIsSep_of_scan{Value,Key,BlockEntry}` at `s`: the step consumed a block-context
    indicator (`peekBack?`) and emitted it. -/
def rowNextIsSepInd (s : ScannerState) : Rule2Row :=
  let hyp := !s.inFlow && (match s.peekBack?, lastReal s with
    | some ':', some .value => true
    | some '?', some .key => true
    | some '-', some .blockEntry => true
    | _, _ => false)
  .of hyp (nextIsSepB s)

/-- `nextIsSep_of_propertyFollowerOk` at `s`: the step emitted a block-context property. -/
def rowNextIsSepProp (s : ScannerState) : Rule2Row :=
  let hyp := !s.inFlow && (match lastReal s with
    | some (.anchor _) | some (.tag _ _) => true
    | _ => false)
  .of hyp (nextIsSepB s)

/-- `content_park_gate` at `s`: a content token parked before `#` at column > 0 has a white
    run behind it (so the comment's `[66]` separator is real), i.e. `CommentOk` never fires
    on an empty run. -/
def rowContentGate (s : ScannerState) : Rule2Row :=
  let hyp := s.col != 0 && s.peek? == some '#'
    && (match lastReal s with | some t => isContentTok t | none => false)
  let whiteBehind := match s.peekBack? with
    | some c => isWhiteSpaceBool c
    | none => false
  .of hyp (whiteBehind && commentOkB s)

/-- `jsonKeyBefore_scanValue` at `(s, s')`: a flow `:` step (`scanValue`) writes the key marker and
    preserves the key's JSON-ness — `jsonKeyBefore` after equals `jsonKeyOfLast` before. -/
def rowJsonCarry (p : ScannerState × ScannerState) : Rule2Row :=
  let (s, s') := p
  let hyp := s.inFlow && s.peek? == some ':' && lastReal s' == some .value
  .of hyp (L4YAML.Proofs.StreamAccum.jsonKeyBefore s'.tokens == L4YAML.Proofs.StreamAccum.jsonKeyOfLast s.tokens)

/-- `jsonKeyOfLast_of_glued` at `s`: the dispatcher pauses on a flow `:` whose follower is glued
    (not blank, not a flow indicator) and `isValueCandidate` accepts — then the key was JSON-like. -/
def rowJsonGlued (s : ScannerState) : Rule2Row :=
  let glued := match s.peekAt? 1 with
    | some n => !(isBlankBool n || isFlowIndicatorBool n)
    | none => false
  let hyp := s.inFlow && s.peek? == some ':' && glued && isValueCandidate s
  .of hyp (L4YAML.Proofs.StreamAccum.jsonKeyOfLast s.tokens)

def col0Inputs : List String :=
  ["a: b", "a:\n  b", "? a\n: b", "- a", "- - a", "&x a", "!t a", "!!str a", "&x !t a", "a #b",
   "a: b #c", "\"a\" #b", "'a' #b", "[a] #b", "{a: b} #c", "- a #b", "*x #b", "a: |\n  x\n#c",
   "a:\n#c\n  b", "- &x a", "? &x a\n: !t b", "{\"a\":b}", "{\"a\":[1]}", "{\"a\" :b}", "{'a':{b: c}}",
   "{[a]:[1]}", "{{a: b}:[1]}", "[\"a\":b]", "[\"a\":[1]]", "{a: b}", "{a :b}", "[a, b: c]",
   "{\"a\":&x b}", "{\"a\":!t b}", "{\"a\":*x}", "{\"a\":\n b}", "k: {\"a\":b}", "k: [\"a\":b, c]",
   "{x: 1, \"a\":[1]}", "{a:[1]}", "[a:{b: c}]", "{? \"a\": b}", "{? a: b}", "[? a: b]", "[]", "{}", ""]

def testColZeroParks (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 25: [66] col-0 parks (NextIsSep / content_park_gate / JSON-key carry)"
  let mut tally : Array (Nat × Nat × Nat) := #[(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)]
  let bump (t : Nat × Nat × Nat) : Rule2Row → Nat × Nat × Nat
    | .failedHyp => (t.1 + 1, t.2.1, t.2.2)
    | .holds => (t.1, t.2.1 + 1, t.2.2)
    | .refuted => (t.1, t.2.1, t.2.2 + 1)
  let mut states := 0
  for input in col0Inputs do
    let pairs := stepPairs input
    states := states + pairs.length
    for (p, i) in pairs.zipIdx do
      let s := p.2
      let rows := [rowNextIsSepInd s, rowNextIsSepProp s, rowContentGate s, rowJsonCarry p, rowJsonGlued p.1]
      for (r, k) in rows.zipIdx do
        tally := tally.modify k (bump · r)
        checkM state s!"col0/{input.quote}/step {i}/row {k}: not refuted" (r != .refuted)
          s!"peek={repr s.peek?} back={repr s.peekBack?} col={s.col} inFlow={s.inFlow} last={repr (lastReal s)}"
  checkM state "col0/states" (states == 201) s!"states={states}"
  -- (failedHyp, holds, refuted) per row: NextIsSep indicators, NextIsSep properties, content gate,
  -- JSON-key carry, JSON-key glued — `refuted` is 0 on every row; the tallies are pinned so a hypothesis
  -- that fails everywhere is caught (§7).
  checkM state "col0/tally" (tally == #[(185, 16, 0), (193, 8, 0), (198, 3, 0), (178, 23, 0), (194, 7, 0)]) s!"tally={repr tally}"

/-! ## Priority 26 — the `?`'s own mark (item 357, row 12)

`scanKey_markedCols` / `dispatchBlockIndicators_markedCols`: at every block-indicator step
the marked columns after the step lie in `s_prep.col :: before`, and when the indicator is a
block `?` its own column IS newly marked.  Walked on real scans, including nested, compact
(`? ? a`, `- ? a`), document-marker and flow inputs (flow `?` marks nothing). -/

/-- Walk `scanNextToken` from `mk'`; at every block step whose preprocessed char is `?`
    outside flow and that emitted a token, check (a) marks after ⊆ `col :: before` and (b) the
    `?` column is marked afterwards.  Returns `(questionSteps, badSubset, badOwnMark)`. -/
def walkQuestionMark (input : String) : Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut fuel := 64
  let mut q := 0
  let mut bad := 0
  let mut own := 0
  while fuel > 0 do
    fuel := fuel - 1
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      match scanNextToken s with
      | .ok (some s') =>
        if c == '?' && !sp.inFlow && s'.tokens.size > s.tokens.size then
          q := q + 1
          let before := markedColsOf sp.pendingKeys sp.indentColumns
          let after := markedColsOf s'.pendingKeys s'.indentColumns
          let col := (sp.col : Int).toNat
          if !(after.all fun x => x == col || before.contains x) then bad := bad + 1
          if !(after.contains col) then own := own + 1
        s := s'
      | _ => fuel := 0
    | _ => fuel := 0
  return (q, bad, own)

/-- Walk `scanNextToken` from `mk'`; at every block step whose preprocessed char is `-` or `:`
    outside flow and that emitted a token (`dispatchBlockIndicators_markedCols_of_ne`'s domain:
    the dispatcher succeeded on a non-`?` indicator), check that the marks after the step are
    EXACTLY a subset of the marks before — no new mark, not even the top level's column (the
    Priority 24 walk allows that column; this one refutes it).  Returns `(steps, bad)`. -/
def walkNonQuestionNoMark (input : String) : Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut fuel := 64
  let mut n := 0
  let mut bad := 0
  while fuel > 0 do
    fuel := fuel - 1
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      match scanNextToken s with
      | .ok (some s') =>
        if (c == '-' || c == ':') && !sp.inFlow && s'.tokens.size > s.tokens.size then
          n := n + 1
          let before := markedColsOf sp.pendingKeys sp.indentColumns
          let after := markedColsOf s'.pendingKeys s'.indentColumns
          if !(after.all fun x => before.contains x) then bad := bad + 1
        s := s'
      | _ => fuel := 0
    | _ => fuel := 0
  return (n, bad)

def testQuestionMarkColumn (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 26: the `?`'s own mark — scanKey_markedCols (item 357)"
  -- `(input, block `?` steps expected)`; flow `?` and the `?` after `: ` on one line are not
  -- block `?` steps.
  let walks : List (String × Nat) :=
    [("? a", 1), ("? a\n: b", 1), ("?\n  ? a\n: b", 2), ("? ? a", 2), ("- ? a", 1),
     ("? - a", 1), ("a: ? b", 0), ("?\n  ?\n    ? -\n: w", 3), ("{ ? a : b }", 0), ("[? a]", 0),
     ("?\n  ? a\n  ? b\nc: 1", 3), ("? a\n? b\n: c", 2), ("---\n? a", 1), ("&p\n? x\n: v", 1),
     ("?\n  a: b\n  ? c\n: w", 2), ("- - ? a", 1), ("? : v", 1), ("?\n- a", 1), ("k:\n  ?\nb: 2", 1)]
  for (input, expectedQ) in walks do
    let (q, bad, own) := walkQuestionMark input
    checkM state s!"questionMark/{repr input}: block `?` steps" (q == expectedQ)
      s!"q {q} expected {expectedQ}"
    checkM state s!"questionMark/{repr input}: marks after ⊆ `?` col :: before" (bad == 0)
      s!"bad {bad}"
    checkM state s!"questionMark/{repr input}: the `?` column is marked" (own == 0)
      s!"own {own}"

  -- The non-`?` transports (`dispatchBlockIndicators_markedCols_of_ne`, via `scanBlockEntry_markedCols`
  -- and `scanValue_markedCols`): `(input, non-`?` block indicator steps expected)` — no marks (empty),
  -- one enclosing `?` (singleton), nested `?`s, the indicator first/middle/last, after `---`, after a
  -- dedent, compact forms.  At every such step the marks after are a subset of the marks before.
  let noMarkWalks : List (String × Nat) :=
    [("- a", 1), ("a: b", 1), ("- a\n- b", 2), ("a: b\nc: d", 2), ("? a\n: b", 1),
     ("?\n  - a\n: b", 2), ("?\n  a: b\n: c", 2), ("?\n  ? a\n  : b\n: c", 2),
     ("?\n  ?\n    - a\n  : b\n: c", 3), ("- ? a\n  : b", 2), ("? - a\n: - b", 3),
     ("- - a\n- b", 3), ("---\n- a", 2), ("---\n? a\n: b", 2), ("k:\n  - a\nb: 2", 3),
     ("?\n  k:\n    - a\n: v", 3), ("? a: b\n: c", 2), ("- a\n? b\n: c", 1), ("{ a: b }", 0),
     ("[- a]", 0)]
  for (input, expectedN) in noMarkWalks do
    let (n, bad) := walkNonQuestionNoMark input
    checkM state s!"noMark/{repr input}: non-`?` block indicator steps" (n == expectedN)
      s!"n {n} expected {expectedN}"
    checkM state s!"noMark/{repr input}: marks after ⊆ before (no new mark)" (bad == 0)
      s!"bad {bad}"

/-- Priority 27 (item 358): the K1 lanes of `landing_frame_of_cover`.  At every non-flow
    `-`/`:`/`?` block-indicator step that emitted a token, read the preprocessed state `sp`:
    SIBLING = the landing column is the stack's top (`sp.currentIndent = sp.col`); `payable` =
    sibling ∧ (`?` ∨ the top is a MAPPING level) — the lemma's domain; `fresh` = not sibling
    (the first key of a level: its top is the enclosing one); `other` = sibling on a
    SEQUENCE top under `-`/`:` — the arm's genuine residue; `bad` = a sibling `?` on a
    sequence top (would refute `scanKey_top_not_sequence`).  Returns
    `(payable, fresh, other, bad)`. -/
def walkK1Lanes (input : String) : Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut fuel := 64
  let mut payable := 0
  let mut fresh := 0
  let mut other := 0
  let mut bad := 0
  while fuel > 0 do
    fuel := fuel - 1
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      match scanNextToken s with
      | .ok (some s') =>
        if (c == '-' || c == ':' || c == '?') && !sp.inFlow && s'.tokens.size > s.tokens.size then
          let sibling := sp.currentIndent == (sp.col : Int)
          let mapTop := match sp.indents.back? with
            | some top => !top.isSequence
            | none => false
          if !sibling then fresh := fresh + 1
          else if c == '?' then
            payable := payable + 1
            if !mapTop then bad := bad + 1
          else if mapTop then payable := payable + 1
          else other := other + 1
        s := s'
      | _ => fuel := 0
    | _ => fuel := 0
  return (payable, fresh, other, bad)

open L4YAML.Proofs.IndentStackCover in
/-- Priority 27 (item 358, #104 review): INSTANTIATE `landing_frame_of_cover` rather than
    read its lanes.  At every step of `walkK1Lanes`'s population, build the lemma's `lo`/`ks`
    on the preprocessed state (the dispatch state differs only in `allowDirectives`):
    `ks lo` = the MAPPING levels of `sp.indents` at column ≥ `lo`, as `FrameLevel.map`, so
    `Covered lo ks sp` holds by construction.  Reads, per step:
    `memBad` — every premise holds (`lo ∈ {0, col}`, sibling, `?`/mapping top) but
    `FrameLevel.map col ∉ ks` (a refutation of the lemma; pinned 0);
    `floorFail` — `lo := col + 1` (the floor premise fails) and the conclusion fails;
    `dropFail` — `ks := (ks col).erase (map col)` (`Covered` fails) and the conclusion fails;
    `seqMiss` — a sibling `-`/`:` on a SEQUENCE top (the lane premise fails) and the
    conclusion fails on `ks 0`; `freshMiss` — a non-sibling step whose landing is not a
    mapping frame of `ks 0` (the sibling premise fails and the conclusion fails; reads
    `= fresh`: a fresh landing's column is never on the stack).  Returns `(memBad, floorFail, dropFail, seqMiss, freshMiss)`. -/
def walkK1LemmaInstances (input : String) : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut fuel := 64
  let mut memBad := 0
  let mut floorFail := 0
  let mut dropFail := 0
  let mut seqMiss := 0
  let mut freshMiss := 0
  while fuel > 0 do
    fuel := fuel - 1
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      match scanNextToken s with
      | .ok (some s') =>
        if (c == '-' || c == ':' || c == '?') && !sp.inFlow && s'.tokens.size > s.tokens.size then
          let col := sp.col
          let ks (lo : Nat) : List FrameLevel :=
            sp.indents.toList.filterMap fun e =>
              if !e.isSequence && (lo : Int) ≤ e.column then some (FrameLevel.map e.column.toNat)
              else none
          let hit (l : List FrameLevel) : Bool := l.contains (FrameLevel.map col)
          let sibling := sp.currentIndent == (col : Int)
          let mapTop := match sp.indents.back? with
            | some top => !top.isSequence
            | none => false
          if !sibling then
            if !hit (ks 0) then freshMiss := freshMiss + 1
          else if c == '?' || mapTop then
            if !hit (ks 0) || !hit (ks col) then memBad := memBad + 1
            if !hit (ks (col + 1)) then floorFail := floorFail + 1
            if !hit ((ks col).erase (FrameLevel.map col)) then dropFail := dropFail + 1
          else
            if !hit (ks 0) then seqMiss := seqMiss + 1
        s := s'
      | _ => fuel := 0
    | _ => fuel := 0
  return (memBad, floorFail, dropFail, seqMiss, freshMiss)

/-- Priority 28 (item 359): the register after an EXPLICIT `:`.  After every successful
    `scanNextToken`, read `(tokens.size, explicitKeyLine, pendingKeys)`; the K7 faces at the
    `:`/compact producers are payable by `ExplicitValueRefused` exactly when the `?` they close
    is the OUTERMOST marked slot (`? a⏎: b` → `none`), and not when an enclosing `?` is still
    marked (`?⏎  ? a⏎  : b⏎: c` → `some 0` at `: b`). -/
def walkExplicitColonRegister (input : String) : List (Nat × Option Nat × List (Option Nat)) :=
  Id.run do
    let mut s := ScannerState.mk' input
    let mut out := []
    let mut fuel := 32
    while fuel > 0 do
      fuel := fuel - 1
      match scanNextToken s with
      | .ok (some s') =>
        out := out ++ [(s'.tokens.size, s'.explicitKeyLine, s'.pendingKeys.toList)]
        s := s'
      | _ => fuel := 0
    return out

/-- Priority 28 (item 359): INSTANTIATE `scanValue_refused_of_outer` at every `:` step.  On the
    dispatch state read its decidable premises — block context, `MarkedColsIn s [col]` (every
    marked slot's column is the `:`'s), and the simple key, if possible, at the cursor's column —
    and the conclusion on the scanned state (`explicitKeyLine = none`).  Returns
    `(payable, bad, nested, nestedLive)`: `payable` = steps where every premise holds, `bad` =
    those whose conclusion fails (a refutation; pinned 0), `nested` = `:` steps with a marked
    slot at another column (the `MarkedColsIn` premise withdrawn), `nestedLive` = those whose
    register stays live (the premise is load-bearing; pinned = `nested` on the inputs below). -/
def walkOuterColon (input : String) : Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut fuel := 32
  let mut payable := 0
  let mut bad := 0
  let mut nested := 0
  let mut nestedLive := 0
  while fuel > 0 do
    fuel := fuel - 1
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      match scanNextToken s with
      | .ok (some s') =>
        if c == ':' && sp.flowLevel == 0 then
          let cols := sp.indentColumns
          let marksAt (col : Nat) : Bool := Id.run do
            let mut ok := true
            for i in [0:sp.pendingKeys.size] do
              match sp.pendingKeys[i]? with
              | some (some _) =>
                match cols[i]? with
                | some ci => if ci.toNat != col then ok := false
                | none => ok := false
              | _ => pure ()
            return ok
          let keyOk := !sp.simpleKey.possible || sp.simpleKey.pos.col == sp.col
          if marksAt sp.col && keyOk then
            payable := payable + 1
            if s'.explicitKeyLine.isSome then bad := bad + 1
          else if !marksAt sp.col then
            nested := nested + 1
            if s'.explicitKeyLine.isSome then nestedLive := nestedLive + 1
        s := s'
      | _ => fuel := 0
    | _ => fuel := 0
  return (payable, bad, nested, nestedLive)

/-- Priority 28 (item 359, #106 review): the ARRAY lemmas behind the payer, instantiated on arrays
    the scanner never builds.  `go cols pks n` reads only `pks[i]` for `i < n`, and
    `PendingKeys.innermost cols pks = go cols pks pks.size` (`innermost_eq_go`), so
    `innermost cols (pks.extract 0 n)` IS `go cols pks n` on the prefix: for every `(cols, pks, n)`
    below, the premise of `go_fst_none_of_noMarks` (no `some (some l)` below `n`) must give `.1 = none`
    (and `.2 = -1`, `go_none_snd`), and the premise of `go_fst_some_of_marked` (some `i < n` marked)
    must give `.1 ≠ none`.  Returns `(cases, noneBad, someBad)`. -/
def walkInnermostArrays : Nat × Nat × Nat := Id.run do
  let colsA : List (Array Int) := [#[], #[0], #[0, 2], #[0, 2, 4], #[-1, 0, 2], #[0, 0]]
  let pksA : List (Array (Option Nat)) :=
    [#[], #[none], #[some 1], #[none, none], #[none, some 0], #[some 0, none], #[some 1, some 3],
     #[none, some 2, none], #[some 0, none, some 5], #[none, none, some 2], #[some 7, some 0, none],
     #[none, none, none, some 1], #[some 1, none, none, none]]
  let mut cases := 0
  let mut noneBad := 0
  let mut someBad := 0
  for cols in colsA do
    for pks in pksA do
      for n in [0, 1, 2, 3, 4] do
        cases := cases + 1
        let pre := pks.extract 0 n
        let r := PendingKeys.innermost cols pre
        let marked := (List.range n).any fun i =>
          match pks[i]? with
          | some (some _) => true
          | _ => false
        if !marked then
          if r.1.isSome || r.2 != -1 then noneBad := noneBad + 1
        else
          if r.1.isNone then someBad := someBad + 1
  return (cases, noneBad, someBad)

/-- Priority 29 (item 360): the carrier's simple-key conjunct, instantiated at EVERY preprocess
    step — `preprocess_saved_key_col` says that with the park's flag up and no flow the prepared
    state's key is possible and sits at the cursor (`pos.col = col`).  Returns `(steps, bad)`:
    `steps` = preprocess steps with `sc.simpleKeyAllowed ∧ ¬ s_prep.inFlow`, `bad` = those whose
    prepared key is impossible or right/left of the cursor (a refutation; pinned 0). -/
def walkSavedKeyAtCursor (input : String) : Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut fuel := 48
  let mut steps := 0
  let mut bad := 0
  while fuel > 0 do
    fuel := fuel - 1
    match scanNextToken_preprocess s with
    | .ok (some (sp, _)) =>
      if s.simpleKeyAllowed && !sp.inFlow then
        steps := steps + 1
        if !sp.simpleKey.possible || sp.simpleKey.pos.col != sp.col then bad := bad + 1
      match scanNextToken s with
      | .ok (some s') => s := s'
      | _ => fuel := 0
    | _ => fuel := 0
  return (steps, bad)

/-- Priority 29 (item 360, #108 review): INSTANTIATE `refused_of_outer_disp` itself.  At every
    `:` preprocess step build the lemma's own dispatch state — the directive-reset twin of
    `s_prep` when `allowDirectives` is up, `s_prep` otherwise — read the decidable premises on
    it (no flow, `MarkedColsIn s_prep [s_prep.col]`, the simple key, if possible, at the cursor)
    and run `scanNextToken_dispatchBlockIndicators … ':'` on THAT state, checking the
    conclusion `explicitKeyLine = none` on its output.  Returns
    `(payable, bad, reset, nested, nestedLive)`: `payable` = steps where every premise holds and
    the dispatch answers `.ok (some _)`, `bad` = those whose register stays live (a refutation;
    pinned 0), `reset` = the payable steps that went through the reset twin (the lemma's first
    branch; pinned ≥ 1 across the inputs), `nested` = `:` steps with a marked slot at another
    column (the `MarkedColsIn` premise withdrawn), `nestedLive` = those whose register stays
    live (the premise is load-bearing; pinned = `nested`). -/
def walkRefusedDisp (input : String) : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut fuel := 32
  let mut payable := 0
  let mut bad := 0
  let mut reset := 0
  let mut nested := 0
  let mut nestedLive := 0
  while fuel > 0 do
    fuel := fuel - 1
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      if c == ':' then
        let sd := if sp.allowDirectives then
          { sp with allowDirectives := false, documentEverStarted := true } else sp
        let cols := sp.indentColumns
        let marksAt (col : Nat) : Bool := Id.run do
          let mut ok := true
          for i in [0:sp.pendingKeys.size] do
            match sp.pendingKeys[i]? with
            | some (some _) =>
              match cols[i]? with
              | some ci => if ci.toNat != col then ok := false
              | none => ok := false
            | _ => pure ()
          return ok
        let keyOk := !sp.simpleKey.possible || sp.simpleKey.pos.col == sp.col
        if !sd.inFlow then
          match scanNextToken_dispatchBlockIndicators sd ':' with
          | .ok (some s') =>
            if marksAt sp.col && keyOk then
              payable := payable + 1
              if sp.allowDirectives then reset := reset + 1
              if s'.explicitKeyLine.isSome then bad := bad + 1
            else if !marksAt sp.col then
              nested := nested + 1
              if s'.explicitKeyLine.isSome then nestedLive := nestedLive + 1
          | _ => pure ()
      match scanNextToken s with
      | .ok (some s') => s := s'
      | _ => fuel := 0
    | _ => fuel := 0
  return (payable, bad, reset, nested, nestedLive)

def testExplicitColonRegister (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 28: register after the explicit `:` (item 359)"
  let walks : List (String × List (Nat × Option Nat × List (Option Nat))) :=
    [("? a\n: b",
      [(4, some 0, [none, some 0]), (7, some 0, [none, some 0]), (10, none, [none, none]),
       (13, none, [none, none])]),
     ("?\n  ? a\n  : b\n: c",
      [(4, some 0, [none, some 0]), (8, some 1, [none, some 0, some 1]),
       (11, some 1, [none, some 0, some 1]), (14, some 0, [none, some 0, none]),
       (17, some 0, [none, some 0, none]), (21, none, [none, none]), (24, none, [none, none])]),
     ("? a: b\n: c",
      [(4, some 0, [none, some 0]), (7, some 0, [none, some 0]), (8, some 0, [none, some 0, none]),
       (11, some 0, [none, some 0, none]), (15, none, [none, none]), (18, none, [none, none])]),
     ("- ? a\n  : b",
      [(4, none, [none, none]), (8, some 0, [none, none, some 0]), (11, some 0, [none, none, some 0]),
       (14, none, [none, none, none]), (17, none, [none, none, none])]),
     ("---\n? a\n: b",
      [(3, none, [none]), (7, some 1, [none, some 1]), (10, some 1, [none, some 1]),
       (13, none, [none, none]), (16, none, [none, none])]),
     ("? ? a\n  : b\n: c",
      [(4, some 0, [none, some 0]), (8, some 0, [none, some 0, some 0]),
       (11, some 0, [none, some 0, some 0]), (14, some 0, [none, some 0, none]),
       (17, some 0, [none, some 0, none]), (21, none, [none, none]), (24, none, [none, none])]),
     ("a: 1\n? b\n: 2",
      [(3, none, [none]), (4, none, [none, none]), (7, none, [none, none]), (10, some 1, [none, some 1]),
       (13, some 1, [none, some 1]), (16, none, [none, none]), (19, none, [none, none])])]
  for (input, expected) in walks do
    let got := walkExplicitColonRegister input
    checkM state s!"explicitColon/{repr input}: (tokens, explicitKeyLine, pendingKeys) per step"
      (got == expected) s!"got {repr got}"
  -- The discriminator the K7 payment reads: after an explicit `:` the register is `none`
  -- iff no slot stays marked.
  for (input, _) in walks do
    let bad := (walkExplicitColonRegister input).filter fun (_, ekl, pks) =>
      (ekl.isNone) != (pks.all fun o => o.isNone)
    checkM state s!"explicitColon/{repr input}: explicitKeyLine = none ⇔ no marked slot" (bad.isEmpty)
      s!"{bad.length} step(s) disagree"
  -- `scanValue_refused_of_outer` instantiated: every payable `:` kills the register; every
  -- nested `:` (a mark at another column) keeps it live.
  let outer : List (String × Nat × Nat) :=
    [("? a\n: b", 1, 0), ("?\n  ? a\n  : b\n: c", 1, 1), ("? a: b\n: c", 1, 1),
     ("- ? a\n  : b", 1, 0), ("---\n? a\n: b", 1, 0), ("? ? a\n  : b\n: c", 1, 1),
     -- an implicit key's `:` (`a: 1`, `k:`) has its simple key BEFORE the cursor: neither premise
     -- lane, so only the `?`'s `:` counts
     ("a: 1\n? b\n: 2", 1, 0), ("? a\n:", 1, 0), ("? earth: blue\n  : x", 0, 2),
     ("k:\n  ? a\n: v", 1, 0)]
  for (input, expPay, expNested) in outer do
    let (payable, bad, nested, nestedLive) := walkOuterColon input
    checkM state s!"outerColon/{repr input}: payable `:` steps" (payable == expPay)
      s!"got {payable}, expected {expPay}"
    checkM state s!"outerColon/{repr input}: no payable `:` keeps the register" (bad == 0)
      s!"{bad} refutation(s)"
    checkM state s!"outerColon/{repr input}: nested `:` steps" (nested == expNested)
      s!"got {nested}, expected {expNested}"
    checkM state s!"outerColon/{repr input}: every nested `:` keeps the register live"
      (nestedLive == nested) s!"{nestedLive}/{nested}"
  -- The array lemmas on arbitrary arrays and bounds (6 column arrays × 13 slot arrays × n ∈ 0..4).
  let (cases, noneBad, someBad) := walkInnermostArrays
  checkM state "innermostArrays: 390 (cols, pks, n) cases" (cases == 390) s!"got {cases}"
  checkM state "innermostArrays: no mark below n ⇒ innermost (none, -1) (go_fst_none_of_noMarks, go_none_snd)"
    (noneBad == 0) s!"{noneBad} refutation(s)"
  checkM state "innermostArrays: a mark below n ⇒ innermost.1 ≠ none (go_fst_some_of_marked)"
    (someBad == 0) s!"{someBad} refutation(s)"
  -- Priority 29 (item 360): the carrier's key conjunct at every flagged block preprocess step.
  let keyInputs : List (String × Nat) :=
    [("? a\n: b", 3), ("?\n  ? a\n  : b\n: c", 5), ("? a: b\n: c", 4), ("- ? a\n  : b", 4),
     ("---\n? a\n: b", 4), ("a: 1\n? b\n: 2", 4), ("k:\n  ? a\n: v", 4), ("- a\n- b: c\n  d: e", 5),
     ("? [a]\n: b", 3), ("a:\n  - b\n  - c: d\n", 5), ("? a\n:", 2), ("x", 1)]
  for (input, expSteps) in keyInputs do
    let (steps, bad) := walkSavedKeyAtCursor input
    checkM state s!"savedKey/{repr input}: flagged block preprocess steps" (steps == expSteps)
      s!"got {steps}, expected {expSteps}"
    checkM state s!"savedKey/{repr input}: every flagged step's key is at the cursor" (bad == 0)
      s!"{bad} refutation(s)"
  -- Priority 29 (item 360, #108 review): the dispatch bridge on its own state scope.  Rows:
  -- `(input, payable, reset, nested)`, pinned from the run; `bad` 0 and `nestedLive = nested`
  -- on every row.  Empty marks (`: b`, the reset twin: the document's first token), the
  -- singleton (`? a⏎: b`), nested (`?⏎  ? a⏎  : b⏎: c`), compact and after-`---`.
  let dispInputs : List (String × Nat × Nat × Nat) :=
    [(": b", 1, 1, 0), (": b\n: c", 2, 1, 0), ("? a\n: b", 1, 0, 0), ("?\n  ? a\n  : b\n: c", 1, 0, 1),
     ("? a: b\n: c", 1, 0, 1), ("- ? a\n  : b", 1, 0, 0), ("---\n? a\n: b", 1, 0, 0),
     ("---\n: b", 1, 0, 0), ("%YAML 1.2\n---\n: b", 1, 0, 0), ("? ? a\n  : b\n: c", 1, 0, 1),
     ("a: 1\n? b\n: 2", 1, 0, 0), ("? a\n:", 1, 0, 0), ("? [a]\n: b", 1, 0, 0), ("k:\n  ? a\n: v", 1, 0, 0)]
  let mut resetTotal := 0
  for (input, expPay, expReset, expNested) in dispInputs do
    let (payable, bad, reset, nested, nestedLive) := walkRefusedDisp input
    resetTotal := resetTotal + reset
    checkM state s!"refusedDisp/{repr input}: payable `:` dispatches" (payable == expPay)
      s!"got {payable}, expected {expPay}"
    checkM state s!"refusedDisp/{repr input}: no payable dispatch keeps the register" (bad == 0)
      s!"{bad} refutation(s)"
    checkM state s!"refusedDisp/{repr input}: reset-twin dispatches" (reset == expReset)
      s!"got {reset}, expected {expReset}"
    checkM state s!"refusedDisp/{repr input}: nested `:` dispatches" (nested == expNested)
      s!"got {nested}, expected {expNested}"
    checkM state s!"refusedDisp/{repr input}: every nested dispatch keeps the register live"
      (nestedLive == nested) s!"{nestedLive}/{nested}"
  checkM state "refusedDisp: the reset branch is exercised (`: b`, `: b⏎: c`)" (resetTotal == 2)
    s!"got {resetTotal}"

/-- Priority 30 (item 361): the flow lane's payer `refused_of_markedCols_nil` — a block state
    with NO marked slot has a dead register.  At every `[`/`{` preprocess step taken from block
    context (`sc.flowLevel = 0`, the state `accum_flow_open_depth0`'s `PackAlt sc` faces are
    typed over) read the marked columns; none ⇒ `explicitKeyLine = none` must hold (`bad`, a
    refutation; pinned 0); some ⇒ the premise is withdrawn and the register is expected live
    (`markedLive`, pinned = `marked`: the premise is load-bearing).  Returns
    `(opens, bad, marked, markedLive)`. -/
def walkFlowOpenRegister (input : String) : Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut fuel := 48
  let mut opens := 0
  let mut bad := 0
  let mut marked := 0
  let mut markedLive := 0
  while fuel > 0 do
    fuel := fuel - 1
    match scanNextToken_preprocess s with
    | .ok (some (_, c)) =>
      if (c == '[' || c == '{') && s.flowLevel == 0 then
        if markedColsOf s.pendingKeys s.indentColumns == [] then
          opens := opens + 1
          if s.explicitKeyLine.isSome then bad := bad + 1
        else
          marked := marked + 1
          if s.explicitKeyLine.isSome then markedLive := markedLive + 1
      match scanNextToken s with
      | .ok (some s') => s := s'
      | _ => fuel := 0
    | _ => fuel := 0
  return (opens, bad, marked, markedLive)

def testFlowOpenRegister (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 30: flow open under an empty marked domain (item 361)"
  -- `(input, opens, marked)`, pinned from the run; `bad` 0 and `markedLive = marked` on every row.
  let rows : List (String × Nat × Nat) :=
    [("[a]: b", 1, 0), ("{a: 1}: c", 1, 0), ("- [a]: b", 1, 0), ("k: [a]", 1, 0), ("k:\n  - [a, b]", 1, 0),
     ("[a]", 1, 0), ("{}", 1, 0), ("---\n[a]: b", 1, 0), ("a: 1\n[1]: b", 1, 0),
     ("? [a]\n: b", 0, 1), ("? {a: 1}\n: b", 0, 1), ("?\n  [a]: b\n: c", 0, 1), ("? a\n: [b]", 1, 0),
     ("- ? [a]\n  : b", 0, 1), ("[[a]]: b", 1, 0),
     -- Item 363: the escape park's opens (`pendingFlow` after `-`/`?`/`:` with nothing between),
     -- read on the block state the open faces are typed over.
     ("- [a]", 1, 0), ("- {a: b}", 1, 0), ("k: {a: b}", 1, 0), ("? [a]", 0, 1), ("- ? [a]\n  : b", 0, 1),
     ("? - [a]\n: b", 0, 1), ("k:\n- [a]\n- {b: c}", 2, 0), ("? a\n: - [b]", 1, 0)]
  for (input, expOpens, expMarked) in rows do
    let (opens, bad, marked, markedLive) := walkFlowOpenRegister input
    checkM state s!"flowOpen/{repr input}: unmarked block opens" (opens == expOpens)
      s!"got {opens}, expected {expOpens}"
    checkM state s!"flowOpen/{repr input}: every unmarked open has a dead register" (bad == 0)
      s!"{bad} refutation(s)"
    checkM state s!"flowOpen/{repr input}: marked block opens" (marked == expMarked)
      s!"got {marked}, expected {expMarked}"
    checkM state s!"flowOpen/{repr input}: every marked open keeps the register live"
      (markedLive == marked) s!"{markedLive}/{marked}"

/-- Priority 31 (item 362): the flow CLOSE lane — the marked-column domain the enclosing block
    park had at the `[`/`{` is still the domain at the `]`/`}` (marks never move inside flow,
    whatever content the node holds — plain/quoted scalars, anchors, aliases, tags: `drift`,
    pinned 0), and when it is empty the register is dead on the block state after the close,
    which is what `refused_of_markedCols_nil` pays `accum_step_flow`'s four CLOSE faces with,
    read off the closed state itself (`bad`, a refutation; pinned 0).  A non-empty domain is
    the withdrawn premise: the register is expected live after the close (`markedLive`,
    pinned = `marked`).  Returns `(closes, bad, drift, marked, markedLive)`. -/
def walkFlowCloseRegister (input : String) : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut fuel := 64
  let mut closes := 0
  let mut bad := 0
  let mut drift := 0
  let mut marked := 0
  let mut markedLive := 0
  let mut dom : Option (List Nat) := none
  while fuel > 0 do
    fuel := fuel - 1
    match scanNextToken_preprocess s with
    | .ok (some (_, c)) =>
      if (c == '[' || c == '{') && s.flowLevel == 0 then
        dom := some (markedColsOf s.pendingKeys s.indentColumns)
      match scanNextToken s with
      | .ok (some s') =>
        match dom with
        | some d =>
          if markedColsOf s'.pendingKeys s'.indentColumns != d then drift := drift + 1
          if s'.flowLevel == 0 then
            if d == [] then
              closes := closes + 1
              if s'.explicitKeyLine.isSome then bad := bad + 1
            else
              marked := marked + 1
              if s'.explicitKeyLine.isSome then markedLive := markedLive + 1
            dom := none
        | none => pure ()
        s := s'
      | _ => fuel := 0
    | _ => fuel := 0
  return (closes, bad, drift, marked, markedLive)

def testFlowCloseRegister (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 31: flow close under the carried marked domain (item 362)"
  -- `(input, closes, marked)`, pinned from the run; `bad` 0, `drift` 0 and `markedLive = marked`
  -- on every row.
  let rows : List (String × Nat × Nat) :=
    [("[a]: b", 1, 0), ("{a: 1}: c", 1, 0), ("- [a]: b", 1, 0), ("k: [a]", 1, 0), ("k:\n  - [a, b]", 1, 0),
     ("[a]", 1, 0), ("{}", 1, 0), ("---\n[a]: b", 1, 0), ("a: 1\n[1]: b", 1, 0),
     ("? [a]\n: b", 0, 1), ("? {a: 1}\n: b", 0, 1), ("?\n  [a]: b\n: c", 0, 1), ("? a\n: [b]", 1, 0),
     ("- ? [a]\n  : b", 0, 1), ("[[a]]: b", 1, 0), ("{a: [1, 2]}: c", 1, 0), ("? [a, {b: c}]\n: d", 0, 1),
     ("k: [a]\nj: b", 1, 0), ("? [a]\n: [b]", 1, 1), ("[a, [b, {c: d}], e]", 1, 0), ("{a: {b: [1]}}", 1, 0),
     -- every content token kind inside the node (PR #112 review): quoted scalars, anchors,
     -- aliases, tags — alone, as flow keys, and under a `?` park.
     ("[\"a\", 'b']: c", 1, 0), ("[&x a, *x]: b", 1, 0), ("[!!str a, !t b]: c", 1, 0),
     ("{\"a\": 'b', &y c: *y, !!int 1: d}: e", 1, 0), ("k: [\"a\", 'b', &x c, *x, !!str d]", 1, 0),
     ("? [\"a\", &x b, *x, !t c]\n: d", 0, 1), ("? {&a k: \"v\", 'q': !!null ~}\n: *a", 0, 1),
     ("- {\"k\": [&z 'v', *z]}: w", 1, 0), ("? a\n: [\"b\", &c d, *c, !!bool true]", 1, 0),
     ("[? \"a\" : 'b', ? &c d : *c]: e", 1, 0)]
  for (input, expCloses, expMarked) in rows do
    let (closes, bad, drift, marked, markedLive) := walkFlowCloseRegister input
    checkM state s!"flowClose/{repr input}: closes to block under an empty domain" (closes == expCloses)
      s!"got {closes}, expected {expCloses}"
    checkM state s!"flowClose/{repr input}: every such close leaves a dead register" (bad == 0)
      s!"{bad} refutation(s)"
    checkM state s!"flowClose/{repr input}: marks never move inside the flow node" (drift == 0)
      s!"{drift} drifting step(s)"
    checkM state s!"flowClose/{repr input}: closes under a marked domain" (marked == expMarked)
      s!"got {marked}, expected {expMarked}"
    checkM state s!"flowClose/{repr input}: every marked close keeps the register live"
      (markedLive == marked) s!"{markedLive}/{marked}"

def testK1Lanes (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 27: K1 lanes — landing_frame_of_cover (item 358)"
  -- `(input, (payable, fresh, other))`, pinned from the run.
  let walks : List (String × (Nat × Nat × Nat)) :=
    [("a: b", (0, 1, 0)), ("a: b\nc: d", (0, 2, 0)), ("k:\n  a: 1\n  b: 2", (0, 3, 0)),
     ("? a\n: b", (1, 1, 0)), ("?\n  ? a\n  : b\n: c", (2, 2, 0)), ("? a\n? b\n: c", (2, 1, 0)),
     ("- a\n- b: c\n  d: e", (0, 3, 1)), ("- ? a\n  : b", (1, 2, 0)), ("? - a\n: - b", (1, 3, 0)),
     ("k:\n  - a\nb: 2", (0, 3, 0)), ("?\n  k:\n    - a\n: v", (1, 3, 0)), ("? a: b\n: c", (1, 2, 0)),
     ("a:\n  b:\n    c: d\n  e: f\ng: h", (0, 5, 0)), ("- - a: 1\n    b: 2", (0, 4, 0)),
     ("---\n? a\n: b", (1, 2, 0)), ("a: 1\n? b\n: 2", (2, 1, 0)), ("? ? a\n  : b\n: c", (2, 2, 0)),
     ("- a", (0, 1, 0)), ("- a\n- b", (0, 1, 1)), ("k:\n- a\n- b", (2, 1, 0)), ("- - a\n  - b\n- c", (0, 2, 2)),
     ("?\n  - a\n  - b\n: c", (1, 2, 1)), ("{ a: b }", (0, 0, 0)), ("[? a]", (0, 0, 0))]
  for (input, (eP, eF, eO)) in walks do
    let (p, f, o, bad) := walkK1Lanes input
    checkM state s!"k1Lanes/{repr input}: (payable, fresh, other)" (p == eP && f == eF && o == eO)
      s!"got ({p}, {f}, {o}) expected ({eP}, {eF}, {eO})"
    checkM state s!"k1Lanes/{repr input}: no sibling `?` on a sequence top" (bad == 0)
      s!"bad {bad}"
    let (memBad, floorFail, dropFail, seqMiss, freshMiss) := walkK1LemmaInstances input
    checkM state s!"k1Lanes/{repr input}: landing_frame_of_cover holds on ks 0 and ks col" (memBad == 0)
      s!"{memBad} payable step(s) with FrameLevel.map col ∉ ks"
    checkM state s!"k1Lanes/{repr input}: the floor premise is load-bearing (lo := col + 1)"
      (floorFail == p) s!"got {floorFail} expected {p}"
    checkM state s!"k1Lanes/{repr input}: the Covered premise is load-bearing (frame erased)"
      (dropFail == p) s!"got {dropFail} expected {p}"
    checkM state s!"k1Lanes/{repr input}: the lane premise is load-bearing (sequence top)"
      (seqMiss == o) s!"got {seqMiss} expected {o}"
    checkM state s!"k1Lanes/{repr input}: the sibling premise is load-bearing (fresh landing)"
      (freshMiss == f) s!"got {freshMiss} expected {f}"

open L4YAML.Proofs.IndentStackCover in
/-- Priority 33 (item 364; #123 review): INSTANTIATE the K1-fresh cover on
    `pendingBlock.h_closeFV`/`pendingBlockContent.h_closeFV` with the PARK's own witnesses,
    not a frame list rebuilt at each step.  A park is born at every non-flow `-` dispatch
    (first entry or sibling, under a sequence OR a mapping top): `n` := the `-`'s column (the
    sequence width the field bounds `ks` by, `fr.width < n`), `ks` := the mapping levels of
    the birth state strictly left of `n`, `lo := 0` — the shape the producers transport —
    plus the compact arm's literal lane `lo := n + 1`, `ks := []` (`covered_nil_of_top_le`)
    when `currentIndent ≤ n`.  The park stays open while the stack holds its sequence level.
    A park whose cover fails at birth (`k:⏎- a`: `n = 0`, no frame left of the entry) is
    `unborn` — the producers decline it.  At every later non-flow `-`/content/`:`/`?` step the
    carried `Covered lo ks` is read on the POST-step state, a `:`/`?` adding the frame it
    opens to `ks` for good (`scanValue_cover_key` / the `?`'s `[187]` level, then the key-line
    park's `h_closeF`):
    `miss` — a mapping level at or right of `lo` the park's `ks` does not name (a refutation
    of the transports; pinned 0); `framed` — park-steps where a frame of `ks` is still a
    mapping level on the stack, and `erasedFail` — those where `Covered` fails once that frame
    is erased (the premise is load-bearing; must equal `framed`); `consed` — steps that push a sequence level under an
    open park (the K1-seq decline's population); `steps` — the dispatches read. -/
def walkCloseFVCover (input : String) : Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut fuel := 64
  let mut steps := 0
  let mut miss := 0
  let mut framed := 0
  let mut erasedFail := 0
  let mut consed := 0
  let mut unborn := 0
  -- open parks: `(lo, n, ks)`
  let mut parks : List (Nat × Nat × List FrameLevel) := []
  while fuel > 0 do
    fuel := fuel - 1
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      match scanNextToken s with
      | .ok (some s') =>
        if !sp.inFlow && c != '#' && s'.tokens.size > s.tokens.size then
          steps := steps + 1
          let covered (lo : Nat) (ks : List FrameLevel) : Bool :=
            s'.indents.toList.all fun e =>
              e.isSequence || e.column < (lo : Int) || ks.contains (FrameLevel.map e.column.toNat)
          let newMapTop : List FrameLevel := match s'.indents.back? with
            | some top =>
              if !top.isSequence && s'.indents.size > sp.indents.size && (0 : Int) ≤ top.column
              then [FrameLevel.map top.column.toNat] else []
            | none => []
          let mut parks' : List (Nat × Nat × List FrameLevel) := []
          for (lo, n, ks) in parks do
            let ks' := if c == ':' || c == '?' then newMapTop ++ ks else ks
            if !covered lo ks' then miss := miss + 1
            -- a frame of `ks'` the post-step stack still holds at or right of `lo`
            let live := ks'.find? fun k => s'.indents.toList.any fun e =>
              !e.isSequence && (lo : Int) ≤ e.column && e.column == (k.width : Int)
            match live with
            | some k =>
              framed := framed + 1
              if !covered lo (ks'.erase k) then erasedFail := erasedFail + 1
            | none => pure ()
            parks' := (lo, n, ks') :: parks'
          parks := parks'.reverse
          if !parks.isEmpty && s'.indents.size > sp.indents.size then
            match s'.indents.back? with
            | some top => if top.isSequence then consed := consed + 1
            | none => pure ()
          -- parks whose sequence level the step popped are closed
          parks := parks.filter fun (_, n, _) =>
            s'.indents.toList.any fun e => e.isSequence && e.column == (n : Int)
          if c == '-' then
            let n := sp.col
            let ks : List FrameLevel := sp.indents.toList.filterMap fun e =>
              if !e.isSequence && (0 : Int) ≤ e.column && e.column < (n : Int)
              then some (FrameLevel.map e.column.toNat) else none
            let bornCovered (lo : Nat) (ks : List FrameLevel) : Bool :=
              sp.indents.toList.all fun e =>
                e.isSequence || e.column < (lo : Int) || ks.contains (FrameLevel.map e.column.toNat)
            if bornCovered 0 ks then parks := (0, n, ks) :: parks else unborn := unborn + 1
            if sp.currentIndent ≤ (n : Int) then
              if bornCovered (n + 1) [] then parks := (n + 1, n, []) :: parks else unborn := unborn + 1
        s := s'
      | _ => fuel := 0
    | _ => fuel := 0
  return (steps, miss, framed, erasedFail, consed, unborn)

def testCloseFVCover (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 33: the K1-fresh cover rides pendingBlock/pendingBlockContent.h_closeFV (item 364)"
  -- `(input, (steps, framed, consed, unborn))`, pinned from the run (22 inputs, 139 steps, 70 framed park-steps); `miss` must be 0 and
  -- `erasedFail = framed` everywhere.  `unborn` = parks whose cover fails at birth (a `-` at a
  -- mapping key's own column: `k:⏎- a` — `n = 0` leaves no frame left of the entry).
  let walks : List (String × (Nat × Nat × Nat × Nat)) :=
    [("- a", (2, 0, 0, 0)), ("- a\n- b", (4, 0, 0, 0)), ("k:\n- a\n- b", (6, 0, 0, 2)), ("k:\n  - a\n  - b", (6, 4, 0, 0)),
     ("k:\n  - a\nm: 2", (7, 2, 0, 0)), ("- - a\n  - b\n- c", (7, 0, 1, 0)), ("? - a\n: - b", (6, 3, 0, 0)),
     ("?\n  - a\n  - b\n: c", (7, 6, 0, 0)), ("- a: 1\n  b: 2", (7, 10, 0, 0)), ("k:\n  - a: 1\n    b: 2\n  - c", (11, 14, 0, 0)),
     ("a:\n  b:\n    - c\n    - d\n  e: f", (11, 6, 0, 0)), ("- &x a\n- *x", (5, 0, 0, 0)), ("- \"a\"\n- 'b'", (4, 0, 0, 0)),
     ("- !!str a\n- [b]", (5, 0, 0, 0)), ("-\n- b", (3, 0, 0, 0)), ("- - - a", (4, 0, 2, 0)), ("k:\n- ? a\n  : b", (7, 1, 0, 1)),
     ("? a\n: - b\n  - c", (7, 4, 0, 0)), ("- a # c\n- b", (4, 0, 0, 0)), ("k: |\n  x\n- a", (3, 0, 0, 0)),
     ("- a\n-\n  k: v\n  m: w", (9, 20, 0, 0)), ("a:\n- b\n- c: d\n  e: f\nz: y", (14, 0, 0, 2))]
  for (input, (eS, eF, eC, eU)) in walks do
    let (st, miss, framed, erasedFail, consed, unborn) := walkCloseFVCover input
    checkM state s!"closeFVCover/{repr input}: every open park's cover survives the `-`/content/`:`/`?` step" (miss == 0)
      s!"{miss} park-step(s) saw a mapping level at or right of lo the park's ks does not name"
    checkM state s!"closeFVCover/{repr input}: the carried frame list is load-bearing" (erasedFail == framed)
      s!"erasing the head frame failed Covered {erasedFail} of {framed} framed park-steps"
    checkM state s!"closeFVCover/{repr input}: (steps, framed, consed, unborn)"
      (st == eS && framed == eF && consed == eC && unborn == eU)
      s!"got ({st}, {framed}, {consed}, {unborn}) expected ({eS}, {eF}, {eC}, {eU})"

def testTraceOfLeafEvents (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 32: TraceOf leaf trace functions on the slice-2 spans (EVENTSOF §10)"
  -- The only decidable part of `tFlowNode_unique`'s Rule-2 ledger: each leaf trace is a
  -- function of the consumed span, so two derivations of one span agree by `rfl`.
  let tagRows : List (String × List L4YAML.Proofs.Serialization.SerializationWellFormed.Event) :=
    [("!!str", [.useTag "!!"]), ("!<a>", []), ("!t", [.useTag "!"]), ("!", [.useTag "!"])]
  for (span, expected) in tagRows do
    let got := L4YAML.Proofs.Serialization.TraceOf.tagEvents span.toList
    checkM state s!"traceOf/tagEvents {repr span}" (got == expected) s!"got {repr got}"
  let anc := L4YAML.Proofs.Serialization.TraceOf.anchorEvents "&x".toList
  checkM state "traceOf/anchorEvents &x" (anc == [.defineAnchor "x"]) s!"got {repr anc}"
  let ali := L4YAML.Proofs.Serialization.TraceOf.aliasEvents "*y".toList
  checkM state "traceOf/aliasEvents *y" (ali == [.useAlias "y"]) s!"got {repr ali}"
  checkM state "traceOf/[&x *y]: anchor then alias, in span order"
    (anc ++ ali == [.defineAnchor "x", .useAlias "y"]) s!"got {repr (anc ++ ali)}"

/-- Priority 34 (item 365): the CONTENT lane's K7 fact — the eleven `h_alt := trivial`
    sites of `accum_content_pending`/`…_on_pendingBlock_indented`/`…_on_pendingMapValue_indented`
    (and `content_dispatch_after_close`'s stepped alternative) now pay `PackAlt.ofRefused` from
    `refused_of_markedCols_nil` on the PARK's own state `sc`, decided there by `Classical.em
    (MarkedColsIn sc [])`.  At every content dispatch taken from block context (`sc.flowLevel = 0`,
    a token that is not a block/flow indicator, comment or document marker) read the marked
    columns of `sc`; none ⇒ `explicitKeyLine = none` must hold (`bad`, a refutation; pinned 0);
    some ⇒ the premise is withdrawn — the step is the named `nested-?` decline (K8c-b) and the
    register is expected live (`markedLive`, pinned = `marked`: load-bearing).  Returns
    `(contents, bad, marked, markedLive)`. -/
def walkContentRegister (input : String) : Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut fuel := 64
  let mut contents := 0
  let mut bad := 0
  let mut marked := 0
  let mut markedLive := 0
  while fuel > 0 do
    fuel := fuel - 1
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      let indicator := c == '-' || c == ':' || c == '?' || c == '[' || c == '{' || c == ']' ||
        c == '}' || c == ',' || c == '#' || c == '%'
      let marker := sp.col == 0 && (c == '-' || c == '.')
      if !indicator && !marker && s.flowLevel == 0 then
        if markedColsOf s.pendingKeys s.indentColumns == [] then
          contents := contents + 1
          if s.explicitKeyLine.isSome then bad := bad + 1
        else
          marked := marked + 1
          if s.explicitKeyLine.isSome then markedLive := markedLive + 1
      match scanNextToken s with
      | .ok (some s') => s := s'
      | _ => fuel := 0
    | _ => fuel := 0
  return (contents, bad, marked, markedLive)

def testContentRegister (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 34: content dispatch under an empty marked domain (item 365)"
  -- `(input, contents, marked)`, pinned from the run; `bad` 0 and `markedLive = marked` on every row.
  let rows : List (String × Nat × Nat) :=
    [("a", 1, 0), ("a: b", 2, 0), ("- a", 1, 0), ("- a\n- b", 2, 0), ("k:\n  a: b", 3, 0),
     ("k:\n- a\n- b", 3, 0), ("- a: b\n  c: d", 4, 0), ("k: |\n  text", 2, 0), ("k: &x a", 3, 0),
     ("k: !!str a", 3, 0), ("k: 'q'", 2, 0), ("k: \"q\"", 2, 0), ("k: *x", 2, 0),
     -- The `?` KEY's content is marked (the `nested-?` decline); the explicit `:`'s VALUE is not —
     -- the `:` closes the entry and the register is dead again (item 359's K7), so `b` in `? a⏎: b`
     -- is an UNMARKED step.  First pinned (0, 2)-style, refuted by the run: the value lane pays.
     ("? a\n: b", 1, 1), ("? a", 0, 1), ("? a\n: b\nc: d", 3, 1), ("- ? a\n  : b", 1, 1),
     ("? - a\n  - b\n: c", 1, 2), ("?\n  a: b\n: c", 1, 2), ("? a\n: - b\n  - c", 2, 1),
     ("k:\n  ? a\n  : b", 2, 1), ("? &x a\n: b", 1, 2), ("---\na\n...", 1, 0), ("a\n---\nb", 2, 0)]
  for (input, expContents, expMarked) in rows do
    let (contents, bad, marked, markedLive) := walkContentRegister input
    checkM state s!"contentReg/{repr input}: unmarked block content steps" (contents == expContents)
      s!"got {contents}, expected {expContents}"
    checkM state s!"contentReg/{repr input}: every unmarked content step has a dead register" (bad == 0)
      s!"{bad} refutation(s)"
    checkM state s!"contentReg/{repr input}: marked block content steps" (marked == expMarked)
      s!"got {marked}, expected {expMarked}"
    checkM state s!"contentReg/{repr input}: every marked content step keeps the register live"
      (markedLive == marked) s!"{markedLive}/{marked}"

/-- Priority 35 (item 366): K7 at the landed `:` of `accum_block_on_closeThenBlock` — the two
    `h_outer` faces (`compact_open_map` at `nv + 1 + m`, `colon_open_map_explicit` at the landing
    column `k`) now pay when the PARK state's marked columns are exactly `[landing column]`, decided
    in that lemma by `Classical.em` (a projection of its own state `sc`, Rule 8).  At every `:`
    dispatched from block context read the marks of the pre-step state: exactly `[col of the ':']`
    ⇒ `refused_of_outer_disp`'s conclusion `explicitKeyLine = none` must hold on the post-dispatch
    state (`bad`, a refutation; pinned 0); empty ⇒ `other`; nested or elsewhere ⇒ the withdrawn
    premise, the register expected live after the `:` (`markedLive`, pinned = `marked`).  Returns
    `(paid, bad, other, marked, markedLive)`. -/
def walkCloseColonOuter (input : String) : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut fuel := 64
  let mut paid := 0
  let mut bad := 0
  let mut other := 0
  let mut marked := 0
  let mut markedLive := 0
  while fuel > 0 do
    fuel := fuel - 1
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      match scanNextToken s with
      | .ok (some s') =>
        if c == ':' && s.flowLevel == 0 then
          let ms := markedColsOf s.pendingKeys s.indentColumns
          if ms == [sp.col] then
            paid := paid + 1
            if s'.explicitKeyLine.isSome then bad := bad + 1
          else if ms == [] then other := other + 1
          else
            marked := marked + 1
            if s'.explicitKeyLine.isSome then markedLive := markedLive + 1
        s := s'
      | _ => fuel := 0
    | _ => fuel := 0
  return (paid, bad, other, marked, markedLive)

def testCloseColonOuter (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 35: the landed `:` under its own `?` mark (item 366)"
  -- `(input, paid, other, marked)`, pinned from the run; `bad` 0 and `markedLive = marked` on every row.
  let rows : List (String × Nat × Nat × Nat) :=
    [("? a\n: b", 1, 0, 0), ("? a\n: b\n? c\n: d", 2, 0, 0), ("- ? a\n  : b", 1, 0, 0), ("k:\n  ? a\n  : b", 1, 1, 0),
     ("? - a\n  - b\n: c", 1, 0, 0), ("?\n  a: b\n: c", 1, 0, 1), ("? a\n: - b\n  - c", 1, 0, 0),
     ("? ? a\n  : b\n: c", 1, 0, 1), ("? a\n:\n  ? b\n  : c", 2, 0, 0), ("a: b", 0, 1, 0), ("- a: b\n  c: d", 0, 2, 0),
     ("? a", 0, 0, 0), ("? a # c\n: b", 1, 0, 0), ("? &x a\n: !!str b", 1, 0, 0), ("? a\n: b\nc: d", 1, 1, 0),
     ("? |\n  t\n: b", 1, 0, 0), ("? [a]\n: b", 1, 0, 0), ("? a\n: {b: c}", 1, 0, 0)]
  for (input, expPaid, expOther, expMarked) in rows do
    let (paid, bad, other, marked, markedLive) := walkCloseColonOuter input
    checkM state s!"closeColon/{repr input}: `:` under exactly its own mark" (paid == expPaid)
      s!"got {paid}, expected {expPaid}"
    checkM state s!"closeColon/{repr input}: every such `:` leaves the register dead" (bad == 0)
      s!"{bad} refutation(s)"
    checkM state s!"closeColon/{repr input}: `:` under no mark" (other == expOther)
      s!"got {other}, expected {expOther}"
    checkM state s!"closeColon/{repr input}: `:` under other/nested marks" (marked == expMarked)
      s!"got {marked}, expected {expMarked}"
    checkM state s!"closeColon/{repr input}: nested marks keep the register live"
      (markedLive == marked) s!"{markedLive}/{marked}"

/-! ### Priority 36 (item 367): `[82]` as the scanner cuts it.

`scanDirective_prod` now concludes `ScannedDirective` (three bodies, `%YAML` / `%TAG` /
reserved), and `SLDirective` has the same three constructors.  `directiveLineB` is a Bool
mirror of that relation on the directive's own line — the character classes are the scanner's
Bool predicates, the shapes are the constructors' — returning the characters it derives
through (to the break or EOF) or `none`. -/
namespace DirectiveMirror

def nsCharB (c : Char) : Bool :=
  !CharPredicates.isWhiteSpaceBool c && !CharPredicates.isLineBreakBool c &&
    CharPredicates.isPrintableBool c && c != '﻿'

def whiteB (c : Char) : Bool := c == ' ' || c == '\t'
def breakB (c : Char) : Bool := CharPredicates.isLineBreakBool c
def digitB (c : Char) : Bool := c.isDigit
def handleB (c : Char) : Bool := CharPredicates.isWordCharBool c || c == '!'
def uriB (c : Char) : Bool := CharPredicates.isUriCharBool c

/-- The `DirectiveTail` of the lemma: whites, then EOF | break | a separated `#` and its text. -/
def tailB (l : List Char) : Option (List Char) :=
  let ws := l.takeWhile whiteB
  let r := l.dropWhile whiteB
  match r with
  | [] => some []
  | c :: _ =>
    if breakB c then some r
    else if c == '#' && !ws.isEmpty then some (r.dropWhile (fun c => !breakB c))
    else none

/-- `some rest` iff the line from `%` derives one body of `ScannedDirective`; `rest` is the
    remainder at the break/EOF.  The name is maximal by construction (`takeWhile`). -/
def directiveLineB (l : List Char) : Option (String × List Char) :=
  match l with
  | '%' :: r =>
    let name := r.takeWhile nsCharB
    let r := r.dropWhile nsCharB
    if name = ['Y', 'A', 'M', 'L'] then
      let r := r.dropWhile whiteB
      let d1 := r.takeWhile digitB
      let r := r.dropWhile digitB
      match r with
      | '.' :: r =>
        let d2 := r.takeWhile digitB
        let r := r.dropWhile digitB
        if d1.isEmpty || d2.isEmpty then none
        else (tailB r).map (fun t => ("yaml", t))
      | _ => none
    else if name = ['T', 'A', 'G'] then
      let r := r.dropWhile whiteB
      let r := r.dropWhile handleB
      let r := r.dropWhile whiteB
      let r := r.dropWhile uriB
      (tailB r).map (fun t => ("tag", t))
    else
      some ("reserved", r.dropWhile (fun c => !breakB c))
  | _ => none

end DirectiveMirror

/-- Priority 36 (item 367): instantiate `scanDirective_prod` — `scanDirective` accepts the line ⇒
    `ScannedDirective` derives it and ends where the scanner ends.  For each input: scanner ok ∧
    mirror derives, ends agree ⇒ `paid`; scanner ok ∧ mirror refuses or ends elsewhere ⇒ `bad` (a
    refutation of the lemma, pinned 0 per row); scanner refuses ∧ mirror derives ⇒ `wider` (the
    relation admits a line the scanner refuses — not a refutation, but the item pins it 0: the
    narrowing is exact on these rows); both refuse ⇒ `refused`.  Returns
    `(paid, bad, wider, refused, body)` with `body` the derived constructor's name. -/
def walkDirectiveLine (input : String) : Nat × Nat × Nat × Nat × String := Id.run do
  let s := ScannerState.mk' input
  let chars := input.toList
  let mirror := DirectiveMirror.directiveLineB chars
  let body := match mirror with | some (b, _) => b | none => "-"
  match scanDirective s, mirror with
  | .ok s', some (_, rest) =>
    let consumed := chars.take (chars.length - rest.length)
    if s'.offset == (String.ofList consumed).utf8ByteSize then (1, 0, 0, 0, body)
    else (0, 1, 0, 0, body)
  | .ok _, none => (0, 1, 0, 0, body)
  | .error _, some _ => (0, 0, 1, 0, body)
  | .error _, none => (0, 0, 0, 1, body)

def testDirectiveLine (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 36: `[82]` l-directive as the scanner cuts it (item 367)"
  -- `(input, expected body, expected (paid, wider, refused))`; `bad` is 0 on every row.
  let rows : List (String × String × Nat × Nat × Nat) :=
    [ -- %YAML: accepted shapes
      ("%YAML 1.2", "yaml", 1, 0, 0), ("%YAML 1.2\n", "yaml", 1, 0, 0),
      ("%YAML 1.2\n---\n", "yaml", 1, 0, 0), ("%YAML 1.2 # c\n", "yaml", 1, 0, 0),
      ("%YAML 1.2\t#c", "yaml", 1, 0, 0), ("%YAML\t12.34 \t\r\n", "yaml", 1, 0, 0),
      ("%YAML 1.2 # é\n", "yaml", 1, 0, 0), ("%YAML     0.0", "yaml", 1, 0, 0),
      -- %YAML: refused shapes (both sides)
      ("%YAML 1.2#c", "-", 0, 0, 1), ("%YAML 1.2 x", "-", 0, 0, 1), ("%YAML 1.", "-", 0, 0, 1),
      ("%YAML .2", "-", 0, 0, 1), ("%YAML", "-", 0, 0, 1), ("%YAML 1", "-", 0, 0, 1),
      ("%YAML 1.2.3", "-", 0, 0, 1), ("%YAML 1.2 1.2", "-", 0, 0, 1), ("%YAML a.b", "-", 0, 0, 1),
      -- a name that only starts with YAML is a reserved directive
      ("%YAML1.2", "reserved", 1, 0, 0), ("%YAMLX 1.2", "reserved", 1, 0, 0),
      -- %TAG: accepted shapes
      ("%TAG ! tag:x,2000:", "tag", 1, 0, 0), ("%TAG !e! http://x/y\n", "tag", 1, 0, 0),
      ("%TAG !e!", "tag", 1, 0, 0),
      -- [89]: the scanner refuses the EMPTY handle (`invalidTagHandle`); `SLDirective.tag` models [82]
      -- without [89] and still derives, so the relation is WIDER than the scanner on these two rows
      ("%TAG", "tag", 0, 1, 0), ("%TAG\n", "tag", 0, 1, 0),
      ("%TAG !e! x # c", "tag", 1, 0, 0), ("%TAG !! !x\n", "tag", 1, 0, 0),
      ("%TAG !e!\t!a,b%20c", "tag", 1, 0, 0),
      -- `#` is a `[39] ns-uri-char`: `x#c` is the prefix, not a comment (first written as refused; REFUTED by the run)
      ("%TAG !e! x#c", "tag", 1, 0, 0),
      -- %TAG: refused shapes (both sides)
      ("%TAG !e! x y", "-", 0, 0, 1), ("%TAG !e! x [", "-", 0, 0, 1),
      ("%TAG é", "-", 0, 0, 1),
      -- reserved: anything to the line end
      ("%", "reserved", 1, 0, 0), ("%\n---", "reserved", 1, 0, 0), ("% x", "reserved", 1, 0, 0),
      ("%FOO bar baz#c", "reserved", 1, 0, 0), ("%TAGS !e! x y", "reserved", 1, 0, 0),
      ("%yaml 1.2", "reserved", 1, 0, 0), ("%FOO\u0001\n", "reserved", 1, 0, 0),
      ("%\u00A0x", "reserved", 1, 0, 0), ("%FOO\tbar\r\nx", "reserved", 1, 0, 0) ]
  for (input, expBody, expPaid, expWider, expRefused) in rows do
    let (paid, bad, wider, refused, body) := walkDirectiveLine input
    checkM state s!"directive/{repr input}: body" (body == expBody) s!"got {body}, expected {expBody}"
    checkM state s!"directive/{repr input}: scanner ok ⇒ ScannedDirective derives to the scanner's end"
      (bad == 0) s!"{bad} refutation(s)"
    checkM state s!"directive/{repr input}: paid" (paid == expPaid) s!"got {paid}, expected {expPaid}"
    checkM state s!"directive/{repr input}: relation no wider than the scanner" (wider == expWider)
      s!"got {wider}, expected {expWider}"
    checkM state s!"directive/{repr input}: refused by both" (refused == expRefused)
      s!"got {refused}, expected {expRefused}"

/-! ### Priority 36b (item 367, review follow-up): the five directive loops at fuel 0/1/2, and the
TAG handle/prefix partition.  Priority 36 compares `scanDirective` with a whole-line mirror; the
review asked for the loop lemmas (`collectDirectiveNameLoop_prod`, `collectVersionMajorLoop_prod`,
`collectVersionMinorLoop_prod`, `collectTagHandleDirectiveLoop_prod`, `collectTagPrefixLoop_prod`)
to be instantiated on their own, at fuel 0, 1, 2, the exact budget and one past it, and for the
`%TAG !e!x` partition (handle `!e!x`, prefix empty — the maximal handle run, not `!e!` / `x`) to be
read off the scanner's token rather than its final offset. -/

/-- The mirror of one loop at `fuel`: the class run cut at `fuel` characters, plus (major loop only)
    the `.` the loop consumes when fuel remains after the digits.  Returns `(run, consumed bytes)`. -/
def directiveLoopMirror (cls : Char → Bool) (dot : Bool) (chars : List Char) (fuel : Nat) :
    String × Nat :=
  let maxRun := chars.takeWhile cls
  let run := maxRun.take fuel
  let dotTaken := dot && fuel > maxRun.length && (chars.drop maxRun.length).head? == some '.'
  let consumed := run ++ (if dotTaken then ['.'] else [])
  (String.ofList run, (String.ofList consumed).utf8ByteSize)

/-- Run one directive loop on `input` at `fuel` and read it against the mirror.  Returns
    `(budgeted, bad, withdrawn, short)`: `budgeted` = the lemma's hypothesis `fuel ≥ inputEnd -
    offset` holds and the loop returned the MAXIMAL class run with the stop character outside the
    class (the `GStar`/`GNot`/`ScannerSurfCorr` conclusion); `bad` = a refutation (run or offset
    disagree with the mirror, or a budgeted run is not maximal); `withdrawn` = the hypothesis does
    not hold at this fuel (the loop still equals the fuel-cut mirror); `short` = a withdrawn row on
    which maximality FAILS — the lane that shows the fuel hypothesis is load-bearing. -/
def walkDirectiveLoop (which : String) (input : String) (start fuel : Nat) : Nat × Nat × Nat × Nat :=
  Id.run do
  -- `start` characters consumed first: the lemmas quantify over ANY `sc`, and `hfuel` counts the
  -- bytes REMAINING from `sc.offset`, so mid-input starts are their own rows
  let s := (ScannerState.mk' input).advanceN start
  let chars := input.toList.drop start
  let budget := s.inputEnd - s.offset
  let (cls, dot, out) : (Char → Bool) × Bool × (String × ScannerState) :=
    match which with
    | "name"   => (DirectiveMirror.nsCharB, false, collectDirectiveNameLoop s "" fuel)
    | "major"  => (DirectiveMirror.digitB, true, collectVersionMajorLoop s "" fuel)
    | "minor"  => (DirectiveMirror.digitB, false, collectVersionMinorLoop s "" fuel)
    | "handle" => (DirectiveMirror.handleB, false, collectTagHandleDirectiveLoop s "" fuel)
    | _        => (DirectiveMirror.uriB, false, collectTagPrefixLoop s "" fuel)
  let (run, s') := out
  let (mRun, mOff) := directiveLoopMirror cls dot chars fuel
  let agree := run == mRun && s'.offset - s.offset == mOff
  let maxLen := (chars.takeWhile cls).length
  -- the stop character, read off the scanner state: outside the class or EOF (the major loop
  -- past its `.` has already left the digit run; that row's maximality is `run.length == maxLen`)
  let stopOut := (dot && s'.offset > run.utf8ByteSize) ||
    (match s'.peek? with | some c => !cls c | none => true)
  if fuel ≥ budget then
    if agree && stopOut && run.length == maxLen then (1, 0, 0, 0) else (0, 1, 0, 0)
  else
    let short := if run.length < maxLen && !stopOut then 1 else 0
    if agree then (0, 0, 1, short) else (0, 1, 1, short)

/-- The `%TAG` partition the scanner emitted: the `.tagDirective handle prefix` token, if any. -/
def scannerTagPartition (input : String) : Option (String × String) :=
  match scanDirective (ScannerState.mk' input) with
  | .ok s' =>
    match s'.tokens.back? with
    | some tok =>
      match tok.val with
      | .tagDirective h p => some (h, p)
      | _ => none
    | none => none
  | .error _ => none

/-- The `%TAG` partition `SLDirective.tag` derives: whites, a MAXIMAL handle run, whites, a prefix
    run (the mirror of the `GStar`/`GNot`/`GStar`/`GStar` spine of the constructor). -/
def mirrorTagPartition (input : String) : String × String :=
  let rest := (input.toList.drop 4).dropWhile DirectiveMirror.whiteB
  let handle := rest.takeWhile DirectiveMirror.handleB
  let afterH := (rest.drop handle.length).dropWhile DirectiveMirror.whiteB
  let pfx := afterH.takeWhile DirectiveMirror.uriB
  (String.ofList handle, String.ofList pfx)

def testDirectiveLoops (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 36b: directive loops at fuel 0/1/2 + TAG handle/prefix partition (item 367 review)"
  -- empty, singleton, class-run-then-stop, stop-first, `.` after 0/1/2 digits, multi-byte, break
  let inputs : List String :=
    [ "", "Y", "YAML 1.2", "TAG !e! x", "1", "1.", "1.2", "12.34", ".2", "a.b", "!", "!e!",
      "!e!x", "!e! x", "!!", "x", "é", " x", "\n", "%20", "tag:x,2000:", "a b", "#c", "[",
      "!e!%20", "1.\n", "..", "\u00A0" ]
  let mut rows := 0
  let mut budgeted := 0
  let mut withdrawn := 0
  let mut short := 0
  for which in ["name", "major", "minor", "handle", "prefix"] do
    for input in inputs do
      let n := input.length
      -- first / second / third / middle / last character as the start (deduplicated)
      let starts := [0, 1, 2, n / 2, n - 1].filter (· ≤ n) |>.eraseDups
      for start in starts do
       let full := (String.ofList (input.toList.drop start)).utf8ByteSize
       for fuel in [0, 1, 2, full, full + 1] do
        rows := rows + 1
        let (b, bad, w, sh) := walkDirectiveLoop which input start fuel
        checkM state s!"loop/{which}/{repr input}/start {start}/fuel {fuel}: loop = fuel-cut mirror; budgeted ⇒ maximal run, stop outside the class"
          (bad == 0) "refuted"
        budgeted := budgeted + b
        withdrawn := withdrawn + w
        short := short + sh
  -- pinned off the first run (5 loops × 28 inputs × ≤ 5 starts × 5 fuels); no `bad` row on the
  -- first run.  The `start ≥ 1` rows are the mid-input states the lemmas quantify over: `hfuel`
  -- counts the bytes REMAINING from `sc.offset`, so a full-input fuel at offset 0 never visits them
  checkM state "loop rows" (rows == 2125) s!"got {rows}"
  checkM state "loop budgeted rows (hypothesis holds; GStar + GNot + corr read)" (budgeted == 1400)
    s!"got {budgeted}"
  checkM state "loop withdrawn rows (fuel below the budget)" (withdrawn == 725) s!"got {withdrawn}"
  checkM state "loop short rows (withdrawn fuel breaks maximality — hypothesis load-bearing)"
    (short == 344) s!"got {short}"
  -- partition: the scanner's token fields against the constructor's spine.  `none` = refused.
  -- [89] (`isTagHandleShaped`): a collected handle that is not `!`, `!!` or `!word!` is refused
  -- (`invalidTagHandle`), so the maximal-run rows `!e!x`, `!e!x!`, `!a!!b!`, `!e!!x!`, `x`, `` are `none`.
  let partRows : List (String × Option (String × String)) :=
    [ ("%TAG !e!x", none), ("%TAG !e! x", some ("!e!", "x")),
      ("%TAG !e!x!", none), ("%TAG ! !", some ("!", "!")),
      ("%TAG !a!!b! c", none), ("%TAG !e!%20", some ("!e!", "%20")),
      -- the reviewer's shape: the handle run is MAXIMAL, so `!e!x` is the handle and `y` the prefix
      -- (first written as refused; REFUTED by the run — the scanner accepts it)
      ("%TAG !e!x y", none), ("%TAG !e!\tx\n", some ("!e!", "x")),
      ("%TAG", none), ("%TAG x", none),
      -- `[` is a `[39] ns-uri-char`: a prefix, not trailing content (first written as refused; REFUTED)
      ("%TAG !e! [", some ("!e!", "[")),
      ("%TAG !e!,x", some ("!e!", ",x")), ("%TAG !e!!x! y", none) ]
  for (input, expected) in partRows do
    let got := scannerTagPartition input
    checkM state s!"partition/{repr input}: scanner token" (got == expected)
      s!"got {repr got}, expected {repr expected}"
    match got with
    | some hp =>
      let m := mirrorTagPartition input
      checkM state s!"partition/{repr input}: SLDirective.tag's maximal handle = the scanner's" (hp == m)
        s!"scanner {repr hp}, relation {repr m}"
    | none => pure ()

/-- Priority 33 (EVENTSOF §10 slice 3): the Rule-2 ledger of `traceOf_unique` on the
block/document fragment — the PARSER's side of each row.  The grammar side lives in
`Tests/Guards/Proofs/TraceOfBlockAmbiguity.lean`: `a⏎&x` has the traces `[]` and
`[defineAnchor x]` (`implicitContinue`, row 19) and `a: |⏎   x⏎  &x b: *x` has `[]` and
`[defineAnchor x, useAlias x]` (`[173]`'s `SIndentLe` tail).  Each row pins what
`parseYaml` does with the informative input: `some k` = accepted with `k` documents,
`none` = refused.  The two refuted rows show the parser taking ONE reading (grammar
laxity) and NEITHER (scanner/grammar disagreement) respectively. -/
def testTraceOfBlockLedger (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 33: traceOf_unique block/document Rule-2 ledger, parser side (EVENTSOF §10)"
  let rows : List (String × String × Option Nat) :=
    [ ("R1 a⏎&x (REFUTED: [] vs [defineAnchor x]; parser: one doc, plain `a &x`)", "a\n&x", some 1),
      ("R2 a: |⏎   x⏎  &x b: *x (REFUTED: [] vs [defineAnchor x, useAlias x]; parser: neither)",
        "a: |\n   x\n  &x b: *x", none),
      ("R2 cousin a: |⏎   x⏎  y: z (no event; parser refuses the dedent too)", "a: |\n   x\n  y: z", none),
      ("a⏎...⏎&x (unique: the `...` route, two docs)", "a\n...\n&x", some 2),
      ("a: &x b", "a: &x b", some 1),
      ("&x a: b", "&x a: b", some 1),
      ("a:⏎  &x b", "a:\n  &x b", some 1),
      ("a:⏎&x b (grammar: one trace via implicitContinue; parser refuses)", "a:\n&x b", none),
      ("- a⏎  &x (plain continuation, trace [])", "- a\n  &x", some 1),
      ("- a⏎- &x b", "- a\n- &x b", some 1),
      ("? a⏎: &x b", "? a\n: &x b", some 1),
      ("a: *x⏎b: c (parser: undefinedAlias — the row-13 layer, not syntax)", "a: *x\nb: c", none),
      ("&x⏎a: b", "&x\na: b", some 1),
      ("!!str⏎a", "!!str\na", some 1),
      ("&x !!str⏎a: b", "&x !!str\na: b", some 1),
      ("a: |⏎  &x b: *x (literal body is text, trace [])", "a: |\n  &x b: *x", some 1),
      ("a: >⏎  *x (folded body is text, trace [])", "a: >\n  *x", some 1),
      ("a: \"x\"⏎&y b: c", "a: \"x\"\n&y b: c", some 1),
      ("--- &x⏎a", "--- &x\na", some 1),
      ("%TAG !e! tag:x⏎---⏎!e!a b", "%TAG !e! tag:x\n---\n!e!a b", some 1),
      ("--- a⏎--- &x b (two explicit docs)", "--- a\n--- &x b", some 2),
      ("a #c⏎&x: b (grammar: one trace via implicitContinue; parser refuses)", "a #c\n&x: b", none),
      ("a: b # &x (comment, no event)", "a: b # &x", some 1),
      ("- &x⏎  - *x", "- &x\n  - *x", some 1),
      ("&x [*x] in block context", "&x [*x]", some 1),
      ("a: &x⏎  b: *x", "a: &x\n  b: *x", some 1),
      ("BOM &x a", "\uFEFF&x a", some 1),
      ("CRLF a␍⏎&x (R1 with CRLF: parser still one doc)", "a\r\n&x", some 1),
      ("CRLF a: &x b␍⏎", "a: &x b\r\n", some 1) ]
  for (label, src, expected) in rows do
    let got : Option Nat := match L4YAML.TokenParser.parseYaml src with
      | .ok docs => some docs.size
      | .error _ => none
    checkM state s!"traceOf/block ledger {label}" (got == expected)
      s!"parseYaml: {repr got} (docs), expected {repr expected}"

/-! ## Priority 68 — `[211]` explicit-only `implicitContinue`: the narrowed stream's document
count, read against the parser on C4's block/document grid (28 inputs), `a⏎&x`, and a
marker / token / position / fuel grid

`[211] l-yaml-stream ::= l-document-prefix* l-any-document? ( l-document-suffix+
l-document-prefix* l-any-document? | l-document-prefix* l-explicit-document? )*`: a document
that is neither the first nor preceded by `...` starts with `---`.  `docsWalk false` is that
rule as a line walk — the DOCUMENT-START count of `[211]` under `implicitContinue` over
`GOpt SLExplicitDocument`: a content line continues the open document, and opens a bare one
only at the start or after `...`.  It reads where documents start, not whether their bodies
derive (`a⏎: x` counts one document; the grammar refuses it at the node), so it is NOT a
membership oracle: on an accepted row, parser documents = walk is a NECESSARY condition of
`parseYaml ok → SLYamlStream` under the narrowing; on a refused row the walk's count is pinned
beside the refusal (`refusedWalk`), never skipped.  `docsWalk true` mirrors TODAY's constructor (`GOpt
SLAnyDocument`): a column-0 content line inside an open document may ALSO open a second bare
document, so it counts the widest split the broad grammar admits.  Each row pins `parseYaml`'s
(documents, root arity) beside both counts: a row with `broad ≠ explicit` is one the broad
grammar reads two ways — `a⏎&x` (R1) and every opener-sibling input (`a: 1⏎b: 2`: the second
bare document the eight opener lines build today) — and the parser must agree with the
explicit-only count on every accepted row.  Fuel = lines read: the walk at fuel 0 / 1 / 2 is
pinned against the parser on the same line prefix. -/
namespace ExplicitOnlyMirror

inductive DocState where
  | none | opened | closed | directives
  deriving BEq, Repr

/-- `'-'` a `---` line, `'.'` a `...` line, `'#'` blank / comment, `'%'` a directive,
`'c'` content (indented or not). -/
def lineKind (l : String) : Char :=
  match (l.toList.reverse.dropWhile Char.isWhitespace).reverse with
  | [] => '#'
  | '#' :: _ => '#'
  | '%' :: _ => '%'
  | '-' :: '-' :: '-' :: rest =>
    if rest = [] ∨ rest.head? = some ' ' ∨ rest.head? = some '\t' then '-' else 'c'
  | '.' :: '.' :: '.' :: rest =>
    if rest = [] ∨ rest.head? = some ' ' ∨ rest.head? = some '\t' then '.' else 'c'
  | _ => 'c'

def atCol0 (l : String) : Bool :=
  match l.toList with
  | c :: _ => c != ' ' && c != '\t'
  | [] => false

def lines (input : String) : List String :=
  (input.splitOn "\n").map fun l => if l.endsWith "\r" then String.mk l.toList.dropLast else l

/-- Document STARTS the stream grammar's marker structure counts over the first `fuel` lines
(not node membership — see the section header): `broad = false` is the
explicit-only `[211]`, `broad = true` today's `GOpt SLAnyDocument` continuation. -/
def docsWalk (broad : Bool) (input : String) (fuel : Nat) : Nat :=
  go ((lines input).take fuel) 0 .none
where
  go : List String → Nat → DocState → Nat
    | [], n, _ => n
    | l :: ls, n, st =>
      match lineKind l, st with
      | '-', .directives => go ls n .opened
      | '-', _ => go ls (n + 1) .opened
      | '.', _ => go ls n .closed
      | 'c', .opened => go ls (if broad && atCol0 l then n + 1 else n) .opened
      -- a `%` line while a document is open: a plain continuation (explicit-only: no new
      -- document); the broad `.directive` arm would also open a directive document here
      | '%', .opened => if broad then go ls (n + 1) .directives else go ls n .opened
      | 'c', _ => go ls (n + 1) .opened
      | _, _ => go ls n st

/-- A `%` line at column 0 while a document is open is NEVER a directive: `[211]` admits only
`l-explicit-document?` after an unterminated document, so either the open node is a plain scalar
and the line is its continuation (`[69]`: `%` is `ns-plain-char`; `a⏎%YAML 1.2` is the scalar
`a %YAML 1.2`) or no derivation exists and the scanner refuses it (`scanDirective`'s first test,
`directiveAfterContent`; item 138's `PendingNode.dirRoute` builds `single` / `suffixContinue`
only).  Only the broad `.directive` arm of `implicitContinue` reads it as a directive document
— the second reading the narrowing removes. -/
def directiveLineWhileOpen (input : String) : Bool :=
  go (lines input) .none
where
  go : List String → DocState → Bool
    | [], _ => false
    | l :: ls, st =>
      match lineKind l, st with
      | '%', .opened => true
      | '-', _ => go ls .opened
      | '.', _ => go ls .closed
      | 'c', _ => go ls .opened
      | _, _ => go ls st

#guard directiveLineWhileOpen "a\n%YAML 1.2\n---\nb" = true
#guard directiveLineWhileOpen "a\n...\n%YAML 1.2\n---\nb" = false
#guard directiveLineWhileOpen "%YAML 1.2\n---\na" = false

def explicitOnlyDocs (input : String) : Nat := docsWalk false input (lines input).length
def broadDocs (input : String) : Nat := docsWalk true input (lines input).length
#guard explicitOnlyDocs "a\n%YAML 1.2\n---\nb" = 2 ∧ broadDocs "a\n%YAML 1.2\n---\nb" = 3

def parserRow (src : String) : Option (Nat × Nat) :=
  let rootArity : YamlValue → Nat
    | .mapping _ arr => arr.size
    | .sequence _ arr => arr.size
    | _ => 0
  match L4YAML.TokenParser.parseYaml src with
  | .ok docs => some (docs.size, (docs[0]?.map (fun d => rootArity d.value)).getD 0)
  | .error _ => none

-- the walk on the constructor's own smallest instances (`#guard`: a refutation is a build failure)
#guard explicitOnlyDocs "" = 0
#guard explicitOnlyDocs "a" = 1
#guard explicitOnlyDocs "a\n&x" = 1 ∧ broadDocs "a\n&x" = 2
#guard explicitOnlyDocs "a\n...\n&x" = 2 ∧ broadDocs "a\n...\n&x" = 2
#guard explicitOnlyDocs "a\n---\nb" = 2 ∧ broadDocs "a\n---\nb" = 3
#guard explicitOnlyDocs "a: 1\nb: 2" = 1 ∧ broadDocs "a: 1\nb: 2" = 2
#guard docsWalk false "a\n&x" 0 = 0 ∧ docsWalk false "a\n&x" 1 = 1 ∧ docsWalk false "a\n&x" 2 = 1
#guard docsWalk true "a\n&x" 0 = 0 ∧ docsWalk true "a\n&x" 1 = 1 ∧ docsWalk true "a\n&x" 2 = 2

end ExplicitOnlyMirror

open ExplicitOnlyMirror in
def testExplicitOnlyStream (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 68: [211] explicit-only implicitContinue — the narrowed stream's document count against the parser (C4's 28 inputs, a⏎&x, marker/token/position/fuel grid)"
  -- (label, input, parser (docs, arity) or refused, broad ≠ explicit-only)
  let c4 : List (String × String × Option (Nat × Nat) × Bool) :=
    [ ("a: &x b", "a: &x b", some (1, 1), false),
      ("&x a: b", "&x a: b", some (1, 1), false),
      ("a:⏎  &x b", "a:\n  &x b", some (1, 1), false),
      ("a:⏎&x b (row-19 over-acceptance: refused)", "a:\n&x b", none, true),
      ("- a⏎  &x", "- a\n  &x", some (1, 1), false),
      ("- a⏎- &x b", "- a\n- &x b", some (1, 2), true),
      ("a⏎&x (R1)", "a\n&x", some (1, 0), true),
      ("? a⏎: &x b", "? a\n: &x b", some (1, 1), true),
      ("a: *x⏎b: c (undefinedAlias: refused)", "a: *x\nb: c", none, true),
      ("&x⏎a: b", "&x\na: b", some (1, 1), true),
      ("!!str⏎a", "!!str\na", some (1, 0), true),
      ("&x !!str⏎a: b (REFUTED arity 1: the parser reads a tagged scalar, arity 0)", "&x !!str\na: b", some (1, 0), true),
      ("a: |⏎  &x", "a: |\n  &x", some (1, 1), false),
      ("a: >⏎  *x", "a: >\n  *x", some (1, 1), false),
      ("a: \"x\"⏎&y b: c", "a: \"x\"\n&y b: c", some (1, 2), true),
      ("--- &x⏎a", "--- &x\na", some (1, 0), true),
      ("%TAG !e! tag:x⏎---⏎!e!a b", "%TAG !e! tag:x\n---\n!e!a b", some (1, 0), true),
      ("--- a⏎--- &x b", "--- a\n--- &x b", some (2, 0), false),
      ("a⏎...⏎&x", "a\n...\n&x", some (2, 0), false),
      ("a #c⏎&x: b (row 19: refused)", "a #c\n&x: b", none, true),
      ("a: b # &x", "a: b # &x", some (1, 1), false),
      ("- &x⏎  - *x", "- &x\n  - *x", some (1, 1), false),
      ("&x [*x]", "&x [*x]", some (1, 1), false),
      ("a: &x⏎  b: *x", "a: &x\n  b: *x", some (1, 1), false),
      ("BOM &x a", "\uFEFF&x a", some (1, 0), false),
      ("a␍⏎&x (CRLF R1)", "a\r\n&x", some (1, 0), true),
      ("a: &x b␍⏎", "a: &x b\r\n", some (1, 1), false),
      ("a: |⏎   x⏎  &x b: *x (R2: refused)", "a: |\n   x\n  &x b: *x", none, false) ]
  -- `---` / `...` first / middle / last, with and without content; directives; nesting
  let markers : List (String × String × Option (Nat × Nat) × Bool) :=
    [ ("(empty)", "", some (0, 0), false),
      ("a", "a", some (1, 0), false),
      ("---", "---", some (1, 0), false),
      ("...", "...", some (0, 0), false),
      ("--- a", "--- a", some (1, 0), false),
      ("---⏎a", "---\na", some (1, 0), true),
      ("a⏎---", "a\n---", some (2, 0), false),
      ("a⏎...", "a\n...", some (1, 0), false),
      ("...⏎a", "...\na", some (1, 0), false),
      ("---⏎...", "---\n...", some (1, 0), false),
      ("---⏎---", "---\n---", some (2, 0), false),
      ("---⏎a⏎---⏎b", "---\na\n---\nb", some (2, 0), true),
      ("a⏎...⏎b", "a\n...\nb", some (2, 0), false),
      ("a⏎...⏎---⏎b (REFUTED differs=false: `---⏎b` is itself a broad split)", "a\n...\n---\nb", some (2, 0), true),
      ("a⏎---⏎...⏎b", "a\n---\n...\nb", some (3, 0), false),
      ("a⏎---⏎b⏎... (REFUTED differs=false: `---⏎b` splits under the broad grammar)", "a\n---\nb\n...", some (2, 0), true),
      ("%YAML 1.2⏎---⏎a", "%YAML 1.2\n---\na", some (1, 0), true),
      ("a⏎%YAML 1.2⏎---⏎b (REFUTED refused: the `%` line is the plain CONTINUATION `a %YAML 1.2`, then an explicit document — two documents under both the parser and the explicit-only walk; the broad `.directive` arm adds a third reading)", "a\n%YAML 1.2\n---\nb", some (2, 0), true),
      ("a⏎...⏎%YAML 1.2⏎---⏎b (REFUTED differs=false: `---⏎b` splits under the broad grammar)", "a\n...\n%YAML 1.2\n---\nb", some (2, 0), true),
      ("# c⏎a⏎# c", "# c\na\n# c", some (1, 0), false),
      ("a:⏎  b:⏎    c: 1⏎d: 2 (nested, root sibling)", "a:\n  b:\n    c: 1\nd: 2", some (1, 2), true),
      ("a:⏎  b:⏎    c: 1⏎---⏎d: 2 (REFUTED differs=false: `---⏎d: 2` splits under the broad grammar)", "a:\n  b:\n    c: 1\n---\nd: 2", some (2, 1), true),
      ("- a⏎- b⏎---⏎- c", "- a\n- b\n---\n- c", some (2, 2), true) ]
  -- every token kind at column 0 after a bare plain line
  let tokens : List (String × String × Option (Nat × Nat) × Bool) :=
    [ ("a⏎!t x", "a\n!t x", some (1, 0), true),
      ("a⏎*x (REFUTED refused: plain continuation `a *x`)", "a\n*x", some (1, 0), true),
      ("a⏎- x (REFUTED refused: plain continuation `a - x`)", "a\n- x", some (1, 0), true),
      ("a⏎? x (REFUTED refused: plain continuation `a ? x`)", "a\n? x", some (1, 0), true),
      ("a⏎: x (refused)", "a\n: x", none, true),
      ("a⏎[x] (REFUTED refused: plain continuation `a [x]`)", "a\n[x]", some (1, 0), true),
      ("a⏎{x: 1} (refused)", "a\n{x: 1}", none, true),
      ("a⏎\"x\" (REFUTED refused: plain continuation)", "a\n\"x\"", some (1, 0), true),
      ("a⏎'x' (REFUTED refused: plain continuation)", "a\n'x'", some (1, 0), true),
      ("a⏎| (REFUTED refused: plain continuation `a |`)", "a\n|", some (1, 0), true),
      ("a⏎> (REFUTED refused: plain continuation `a >`)", "a\n>", some (1, 0), true),
      ("a⏎# c", "a\n# c", some (1, 0), false),
      ("a⏎b: c (refused)", "a\nb: c", none, true),
      ("a: 1⏎b: 2 (`:` opener's sibling)", "a: 1\nb: 2", some (1, 2), true),
      ("? a⏎b: 2 (`?` opener's sibling)", "? a\nb: 2", some (1, 2), true),
      ("a: [1]⏎b: 2 (flow value, block sibling)", "a: [1]\nb: 2", some (1, 2), true),
      ("[1]: a⏎b: 2 (flow key at the root)", "[1]: a\nb: 2", some (1, 2), true),
      ("k:⏎  a: 1⏎b: 2 (closeThenBlock's root sibling)", "k:\n  a: 1\nb: 2", some (1, 2), true),
      ("&p a: 1⏎b: 2 (props park's sibling)", "&p a: 1\nb: 2", some (1, 2), true) ]
  -- the refused rows, with the walk's own count: the walk is not a membership oracle
  let refusedWalk : List (String × Nat) :=
    [ ("a:\n&x b", 1), ("a: *x\nb: c", 1), ("a #c\n&x: b", 1), ("a: |\n   x\n  &x b: *x", 1),
      ("a\n: x", 1), ("a\n{x: 1}", 1), ("a\nb: c", 1) ]
  for (label, src, expected, differs) in c4 ++ markers ++ tokens do
    let got := parserRow src
    let eo := explicitOnlyDocs src
    let br := broadDocs src
    checkM state s!"explicit-only/parser {label}" (got == expected)
      s!"parser (docs, arity) = {repr got}; expected {repr expected}"
    let dirLine := directiveLineWhileOpen src
    checkM state s!"explicit-only/directive-line {label}"
      (dirLine == (src == "a\n%YAML 1.2\n---\nb") && (!dirLine || got.map Prod.snd == some 0))
      s!"`%` line while a document is open = {dirLine}: the parser folds it into a plain scalar (arity 0) or refuses it; got {repr got}"
    checkM state s!"explicit-only/agree {label}"
      (match got with
       | some (d, _) => d == eo
       | none => refusedWalk.lookup src == some eo)
      s!"parser docs = {repr (got.map Prod.fst)}, explicit-only walk = {eo}; a refused row pins the walk's count ({repr (refusedWalk.lookup src)}): the walk reads document starts, not node membership"
    checkM state s!"explicit-only/broad {label}" ((br != eo) == differs)
      s!"broad = {br}, explicit-only = {eo}; expected differs={differs}"
  -- fuel 0 / 1 / 2: the walk on the first k lines against the parser on that prefix
  for src in ["a\n&x", "a\r\n&x", "a: 1\nb: 2", "a\n---\nb", "a\n...\nb", "---\na\n---\nb", "- a\n- &x b"] do
    for k in [0, 1, 2] do
      let pre := "\n".intercalate ((lines src).take k)
      let eo := docsWalk false src k
      let got := parserRow pre
      checkM state s!"explicit-only/fuel {k} {repr src}"
        (match got with | some (d, _) => d == eo | none => false)
        s!"prefix {repr pre}: parser {repr got}, walk {eo}"

/-! ## Priority 69 — `directiveAfterContent`: a `%` line while a document is open, read at the
parser (Row 19 step (1), re-read before any pay)

The scanner already refuses a directive after content without `...` (`scanDirective`'s first
test, `directiveAfterContent`; item 138's `PendingNode.dirRoute` routes a `%` run through
`single` / `suffixContinue` only).  What the rows read: the ONLY accepted `%`-at-column-0 lines
inside an open document are plain continuations (`[69]`: the open node is a plain scalar and
`%` is `ns-plain-char`), block / flow / quoted alike; every other such line is refused with
`directiveAfterContent` at the line of the content it follows; a `%` at column > 0 is refused
as a character (`[126]` ns-plain-first excludes it), not as a directive. -/
def testDirectiveAfterContent (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 69: directiveAfterContent — a `%` line while a document is open is a plain continuation or a refusal, never a directive"
  -- the first document's leading scalar: through a sequence's first element or a mapping's first
  -- value, so a dropped continuation (`[a⏎%b]` without `%b`) is a failure, not a blank
  let rec firstContent : Nat → YamlValue → String
    | _, YamlValue.scalar s => s.content
    | fuel + 1, YamlValue.sequence _ arr _ _ => (arr[0]?.map (firstContent fuel)).getD "<empty sequence>"
    | fuel + 1, YamlValue.mapping _ arr _ _ => (arr[0]?.map (fun p => firstContent fuel p.2)).getD "<empty mapping>"
    | _, _ => "<other>"
  let firstDoc (docs : Array YamlDocument) : String :=
    (docs[0]?.map (fun d => firstContent 8 d.value)).getD "<no document>"
  -- (label, input, accepted as (documents, first document's leading scalar), or the exact refusal)
  let rows : List (String × String × Option (Nat × String) × Option ScanError) :=
    [ ("a⏎%YAML 1.2⏎---⏎b (plain continuation, then an explicit document)", "a\n%YAML 1.2\n---\nb", some (2, "a %YAML 1.2"), none),
      ("a⏎%TAG ! !x⏎---⏎b", "a\n%TAG ! !x\n---\nb", some (2, "a %TAG ! !x"), none),
      ("a⏎%YAML 1.2 (last line)", "a\n%YAML 1.2", some (1, "a %YAML 1.2"), none),
      ("a⏎% (a lone `%`)", "a\n%", some (1, "a %"), none),
      ("a⏎%YAML 1.2 #c⏎---⏎b (comment after the continuation)", "a\n%YAML 1.2 #c\n---\nb", some (2, "a %YAML 1.2"), none),
      ("a⏎⏎%YAML 1.2⏎---⏎b (empty line folded to a break)", "a\n\n%YAML 1.2\n---\nb", some (2, "a\n%YAML 1.2"), none),
      ("&x a⏎%YAML 1.2⏎---⏎b (anchored plain)", "&x a\n%YAML 1.2\n---\nb", some (2, "a %YAML 1.2"), none),
      ("---⏎a⏎%YAML 1.2⏎---⏎b (inside an explicit document)", "---\na\n%YAML 1.2\n---\nb", some (2, "a %YAML 1.2"), none),
      ("%YAML 1.2⏎---⏎a⏎%YAML 1.2⏎---⏎b (after a real directive document)", "%YAML 1.2\n---\na\n%YAML 1.2\n---\nb", some (2, "a %YAML 1.2"), none),
      ("a⏎%YAML 1.2⏎...⏎%YAML 1.2⏎---⏎b (continuation, then `...`, then a real directive)", "a\n%YAML 1.2\n...\n%YAML 1.2\n---\nb", some (2, "a %YAML 1.2"), none),
      ("[a⏎%b] (flow plain continuation: the sequence's one element)", "[a\n%b]", some (1, "a %b"), none),
      ("- a⏎  %b (continuation at column > 0: the sequence's one element)", "- a\n  %b", some (1, "a %b"), none),
      ("\"a⏎%b\" (quoted: text)", "\"a\n%b\"", some (1, "a %b"), none),
      ("a⏎...⏎%YAML 1.2⏎---⏎b (a directive after `...`: allowed)", "a\n...\n%YAML 1.2\n---\nb", some (2, "a"), none),
      ("a: 1⏎%YAML 1.2⏎---⏎b: 2 (mapping value closed at the dedent)", "a: 1\n%YAML 1.2\n---\nb: 2", none, some (.directiveAfterContent 1)),
      ("- a⏎%YAML 1.2⏎---⏎b (sequence entry closed)", "- a\n%YAML 1.2\n---\nb", none, some (.directiveAfterContent 1)),
      ("a #c⏎%YAML 1.2⏎---⏎b (comment ends the plain scalar)", "a #c\n%YAML 1.2\n---\nb", none, some (.directiveAfterContent 1)),
      ("\"a\"⏎%YAML 1.2⏎---⏎b (quoted scalar closed)", "\"a\"\n%YAML 1.2\n---\nb", none, some (.directiveAfterContent 1)),
      ("a: |⏎  x⏎%YAML 1.2⏎---⏎b (block scalar closed at the dedent)", "a: |\n  x\n%YAML 1.2\n---\nb", none, some (.directiveAfterContent 2)),
      ("[a,⏎%b] (after a flow separator: no plain to continue)", "[a,\n%b]", none, some (.directiveAfterContent 1)),
      ("? a⏎%YAML 1.2⏎---⏎b (explicit key closed)", "? a\n%YAML 1.2\n---\nb", none, some (.directiveAfterContent 1)),
      ("a:⏎  %x (column > 0: `%` cannot start a plain scalar — refused as a character, not a directive)", "a:\n  %x", none, some (.unexpectedChar '%' 1 2)) ]
  for (label, src, accepted, refusal) in rows do
    match L4YAML.TokenParser.parseYaml src, accepted, refusal with
    | .ok docs, some (n, content), _ =>
      checkM state s!"directiveAfterContent/{label}" (docs.size == n && firstDoc docs == content)
        s!"accepted: docs={docs.size} first={repr (firstDoc docs)}; expected {n} / {repr content}"
    | .ok docs, none, _ =>
      checkM state s!"directiveAfterContent/{label}" false
        s!"ACCEPTED (docs={docs.size} first={repr (firstDoc docs)}) but a refusal was expected"
    | .error e, _, some err =>
      checkM state s!"directiveAfterContent/{label}" (toString e == toString err)
        s!"refused: {e}; expected {err}"
    | .error e, _, none =>
      checkM state s!"directiveAfterContent/{label}" false s!"REFUSED ({e}) but acceptance was expected"


/-! ## Priority 70 — the (α) root-frame bound (Row 19, step (2) stage A): a park's frames may
name the park's OWN level, read before the restatement

Stage A restates the `:` park's frame faces (`pendingMapValue.h_closeF`, `deeperLandingResume` /
`closeThenBlock`'s `h_valF`) from `∀ fr ∈ ks, fr.width < n` to `≤ n`.  What the rows read:
(i) the bound shape itself on boundary lists — `[]`, the root frame `[map 0]`, the `-` park's
pair `[seq 0, map 0]` (the enclosing mapping at the sequence's own column), nested lists — `<`
refuses the own-level frame and `≤` admits it; (ii) the scanner's stack at the sibling-after-
sequence landings (`a:⏎- b⏎c: 1`), with fuel 0/1/2 — REFUTED as predicted: the compact `-` at the
mapping's column pushes NO level (item 389: the mapping at `nv = k` is the stack top), so the
scanner never holds a `seq n` over a `map n`; the own-level frame is the PARK's (`map n` at the
`-` park's column), not a scanner level, which is why the `≤` lands on the park faces and
`ResumeFrames.level`'s own `<` stands; (iii) the parser's reading
of those inputs: one document, the root mapping with both keys (the sibling after the compact
sequence resumes the mapping), the `-`-first and column-1 twins refused.
Predictions (scored in the item): P1 every sibling-after-sequence row is one document with two
root keys; P2 the deepest stack of `a:⏎- b⏎c: 1` is `[map 0, map 0, seq 0]` (REFUTED:
`[map 0, map 0]`, no push; fuel 2 already reaches it, not `[map 0]`); P3 `- a⏎b: 1` and `a:⏎- b⏎ c: 1` are refused; P4 fuel 0 projects `[]`. -/
/-! Rule 2 on `ResumeFrames.strict` itself, under a `ResumeFrames` premise (elaboration-time rows; the
exe's rows below can only instantiate the bound on raw lists).  A nested level reads the strict order
off the frame below; the own-level pair `[map 0, map 0]` has NO `ResumeFrames` witness — the equal-width
frame of the `-` park lives on the park's face, never in a level, which is why stage A widens the faces
and not `ResumeFrames.level`. -/
open L4YAML.Surface L4YAML.Proofs.IndentStackCover L4YAML.Proofs.StreamAccum in
example {P : SurfPos → Prop} {sp : SurfPos}
    (h : ResumeFrames P [FrameLevel.map 2, FrameLevel.map 0] sp) : (FrameLevel.map 0).width < 2 :=
  h.strict _ (List.Mem.head _)

open L4YAML.Surface L4YAML.Proofs.IndentStackCover L4YAML.Proofs.StreamAccum in
example {P : SurfPos → Prop} {sp : SurfPos} : ¬ ResumeFrames P [FrameLevel.map 0, FrameLevel.map 0] sp :=
  fun h => absurd (h.strict _ (List.Mem.head _)) (Nat.lt_irrefl _)

open L4YAML.Proofs.IndentStackCover in
def testRootFrameBound (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 70: the (α) root-frame bound — `<` refuses the park's own level, `≤` admits it (stage A)"
  -- (i) the bound shape on boundary lists: (label, list, park level, `<` holds, `≤` holds)
  let lists : List (String × List FrameLevel × Nat × Bool × Bool) :=
    [ ("[] at 0", [], 0, true, true),
      ("[] at 2", [], 2, true, true),
      ("[map 0] at 0 (the root frame at the root park)", [FrameLevel.map 0], 0, false, true),
      ("[map 0] at 2 (an enclosing frame, strictly narrower)", [FrameLevel.map 0], 2, true, true),
      ("[seq 0, map 0] at 0 (the `-` park's pair, one width)", [FrameLevel.seq 0, FrameLevel.map 0], 0, false, true),
      ("[map 2, map 0] at 2 (nested, own level on top)", [FrameLevel.map 2, FrameLevel.map 0], 2, false, true),
      ("[map 2, map 0] at 4 (nested, strictly below)", [FrameLevel.map 2, FrameLevel.map 0], 4, true, true),
      ("[map 4, map 2] at 2 (a wider frame: neither bound)", [FrameLevel.map 4, FrameLevel.map 2], 2, false, false) ]
  for (label, ks, n, eLt, eLe) in lists do
    let gotLt := ks.all (fun fr => decide (fr.width < n))
    let gotLe := ks.all (fun fr => decide (fr.width ≤ n))
    checkM state s!"rootFrameBound/{label}: `<` {eLt}, `≤` {eLe}" (gotLt == eLt && gotLe == eLe)
      s!"got `<` {gotLt}, `≤` {gotLe}"
  -- the `≤` bound is the `<` bound plus the own-level frames, on every list above
  for (label, ks, n, _, _) in lists do
    let viaLt := ks.all (fun fr => decide (fr.width < n || fr.width == n))
    checkM state s!"rootFrameBound/{label}: `≤` = `<` ∨ own level" (viaLt == ks.all (fun fr => decide (fr.width ≤ n))) ""
  -- (ii) the scanner's stack at the sibling-after-sequence landings (P2), with fuel 0/1/2
  checkFrames state "a:⏎- b⏎c: 1 (compact sequence at the mapping's column: no level pushed)" "a:\n- b\nc: 1\n"
    [FrameLevel.map 0, FrameLevel.map 0]
  checkFrames state "a:⏎-⏎c: 1 (empty entry, then the sibling: no level pushed)" "a:\n-\nc: 1\n"
    [FrameLevel.map 0, FrameLevel.map 0]
  checkFrames state "a:⏎- b⏎- c⏎d: 1 (two entries: no level pushed)" "a:\n- b\n- c\nd: 1\n"
    [FrameLevel.map 0, FrameLevel.map 0]
  checkFrames state "a: 1⏎b: 2 (no sequence: mapping levels only)" "a: 1\nb: 2\n"
    [FrameLevel.map 0, FrameLevel.map 0]
  checkFrames state "a:⏎  b: 1⏎c: 2 (nested mapping: widths strictly nest)" "a:\n  b: 1\nc: 2\n"
    [FrameLevel.map 0, FrameLevel.map 0, FrameLevel.map 2]
  checkFrames state "a:⏎  - b⏎c: 1 (indented sequence: the seq level is wider)" "a:\n  - b\nc: 1\n"
    [FrameLevel.map 0, FrameLevel.map 0, FrameLevel.seq 2]
  for (fuel, expected) in [(0, ([] : List FrameLevel)), (1, [FrameLevel.map 0]), (2, [FrameLevel.map 0, FrameLevel.map 0])] do
    let got := deepestFrames "a:\n- b\nc: 1\n" fuel
    checkM state s!"rootFrameBound/fuel {fuel}: deepest stack [{frameLabel expected}]" (got == expected)
      s!"got [{frameLabel got}]"
  -- (iii) the parser: (label, input, documents and root-mapping arity, or refused)
  let rootArity (docs : Array YamlDocument) : Option Nat :=
    docs[0]?.bind (fun d => match d.value with | YamlValue.mapping _ arr _ _ => some arr.size | _ => none)
  let rows : List (String × String × Option (Nat × Option Nat)) :=
    [ ("a:⏎- b⏎c: 1", "a:\n- b\nc: 1", some (1, some 2)),
      ("a:⏎-⏎c: 1", "a:\n-\nc: 1", some (1, some 2)),
      ("a:⏎- b⏎- c⏎d: 1", "a:\n- b\n- c\nd: 1", some (1, some 2)),
      ("a: 1⏎b: 2", "a: 1\nb: 2", some (1, some 2)),
      ("a:⏎  b: 1⏎c: 2", "a:\n  b: 1\nc: 2", some (1, some 2)),
      ("a: [1]⏎b: 2 (flow value, then the sibling)", "a: [1]\nb: 2", some (1, some 2)),
      ("? a⏎: b⏎c: d (explicit entry, then the sibling)", "? a\n: b\nc: d", some (1, some 2)),
      ("a:⏎- b:⏎  - c⏎  d: 1⏎e: 2 (nested seq-over-map, two siblings)", "a:\n- b:\n  - c\n  d: 1\ne: 2", some (1, some 2)),
      ("---⏎a:⏎- b⏎c: 1 (explicit document)", "---\na:\n- b\nc: 1", some (1, some 2)),
      ("a:⏎- b⏎...⏎c: 1 (`...` between: two documents)", "a:\n- b\n...\nc: 1", some (2, some 1)),
      ("a:⏎- b⏎---⏎c: 1 (`---` between: two documents)", "a:\n- b\n---\nc: 1", some (2, some 1)),
      ("a:⏎- b (no sibling: one key)", "a:\n- b", some (1, some 1)),
      ("a (singleton scalar: no mapping)", "a", some (1, none)),
      ("(empty)", "", some (0, none)),
      ("- a⏎b: 1 (`-` first: refused)", "- a\nb: 1", none),
      ("a:⏎- b⏎ c: 1 (sibling at column 1: refused)", "a:\n- b\n c: 1", none) ]
  for (label, src, expected) in rows do
    let got : Option (Nat × Option Nat) := match L4YAML.TokenParser.parseYaml src with
      | .ok docs => some (docs.size, rootArity docs)
      | .error _ => none
    checkM state s!"rootFrameBound/parser {label}" (got == expected) s!"got {repr got}, expected {repr expected}"
/-! ## Priority 71 — Row 19 step (2) stage B, READ before the pay: the (α) root-frame supply's two
facts.  Stage B supplies `[FrameLevel.map 0]` at the root births (the `Or.inl ⟨[], …⟩` fallbacks of
the opener lines) and spends an append on `SCompactMapTail` — the root mapping's tail after the
first entry, continued by the siblings the route resumes.  Rows: (i) the scanner's stack at the
root births (fuel 0/1/2 on the three-key mapping): the root frame is the stack's bottom at every
root `:` / `?` / flow-key park, so the supply names a frame the scanner holds; (ii) the append on
the constructor's own instances (nil/nil, cons/nil, nil/cons, two-each) at `n = 0 / 2`, stated
here first — the library copy lands with the pay; (iii) the parser and the two document walks on
the root births and on `TraceOfBlockAmbiguity`'s two inputs (`a⏎&x`, `a: |⏎   x⏎  &x b: *x`), the
readings the rewrite of that file must keep.
Predictions (scored in the item): P5 every append row elaborates; P6 `a⏎&x` is ONE document,
scalar `a &x` (explicit-only walk 1, broad 2), and `a: |⏎   x⏎  &x b: *x` is REFUSED by the parser
(walks 1 / 2); P8 the deepest stacks are `[map 0, map 0]` at every root mapping birth, `[map 0]`
for `a⏎&x`, `[map 0, seq 0]` for the root `-` park. -/
open L4YAML.Surface in
/-- The append stage B spends, in the shape the pay will state (`lemma`, structural on the tail). -/
private lemma compactMapTail_append_read {n : Nat} : ∀ {s s₁ s₂ : SurfPos},
    SCompactMapTail n s s₁ → SCompactMapTail n s₁ s₂ → SCompactMapTail n s s₂
  | _, _, _, .nil _ _, h₂ => h₂
  | _, _, _, .cons _ s sa sb _ hi he ht, h₂ => .cons _ s sa sb _ hi he (compactMapTail_append_read ht h₂)

open L4YAML.Surface in
example {s : SurfPos} : SCompactMapTail 0 s s := compactMapTail_append_read (.nil 0 s) (.nil 0 s)
open L4YAML.Surface in
example {s s₁ s₂ s' : SurfPos} (hi : SIndent 0 s s₁) (he : SBlockMapEntry 0 s₁ s₂)
    (ht : SCompactMapTail 0 s₂ s') : SCompactMapTail 0 s s' :=
  compactMapTail_append_read (.cons 0 s s₁ s₂ s₂ hi he (.nil 0 s₂)) ht
open L4YAML.Surface in
example {s s₁ s₂ s' : SurfPos} (hi : SIndent 2 s s₁) (he : SBlockMapEntry 2 s₁ s₂)
    (ht : SCompactMapTail 2 s₂ s') : SCompactMapTail 2 s s' :=
  compactMapTail_append_read (.nil 2 s) (.cons 2 s s₁ s₂ s' hi he ht)
open L4YAML.Surface in
example {s s₁ s₂ s₃ s₄ s₅ s₆ : SurfPos} (hi₁ : SIndent 2 s s₁) (he₁ : SBlockMapEntry 2 s₁ s₂)
    (hi₂ : SIndent 2 s₂ s₃) (he₂ : SBlockMapEntry 2 s₃ s₄) (hi₃ : SIndent 2 s₄ s₅)
    (he₃ : SBlockMapEntry 2 s₅ s₆) : SCompactMapTail 2 s s₆ :=
  compactMapTail_append_read (.cons 2 s s₁ s₂ s₂ hi₁ he₁ (.nil 2 s₂))
    (.cons 2 s₂ s₃ s₄ s₆ hi₂ he₂ (.cons 2 s₄ s₅ s₆ s₆ hi₃ he₃ (.nil 2 s₆)))

/-! The append on CONCRETE tails (review of the read item): `[186]`'s `?⏎` entry at indent 0,
built from its characters as `entryQ` is, generalised over the rest of the input — so the tails
below are real derivations over `?⏎?⏎?⏎`, and the appended tail can end nowhere but at the
position the characters force (`⟨[], 0⟩`).  `SIndent 0` is `SIndent.zero`, the only indentation a
column-0 entry has; a `SCompactMapTail 1` over this input has no `cons` at all (`SIndent 1` needs a
space the input lacks), which is why the rows are at `n = 0`. -/
open L4YAML.Surface in
private lemma entryQ_at (rest : List Char) : SBlockMapEntry 0 ⟨'?' :: '\n' :: rest, 0⟩ ⟨rest, 0⟩ :=
  SBlockMapEntry.explicitEmpty 0 _ ⟨'\n' :: rest, 1⟩ _ (GLit.mk ('\n' :: rest) 0)
    (SBlockIndented.empty 0 .blockOut _ _ (sslBreak1 rest))

open L4YAML.Surface in
/-- `?⏎?⏎?⏎` from its first character: one entry, then the tail of two. -/
private lemma tailQ3_1_2 : SCompactMapTail 0 ⟨['?', '\n', '?', '\n', '?', '\n'], 0⟩ ⟨[], 0⟩ :=
  compactMapTail_append_read
    (.cons 0 _ _ ⟨['?', '\n', '?', '\n'], 0⟩ _ (SIndent.zero _) (entryQ_at ['?', '\n', '?', '\n']) (.nil 0 _))
    (.cons 0 _ _ ⟨['?', '\n'], 0⟩ _ (SIndent.zero _) (entryQ_at ['?', '\n'])
      (.cons 0 _ _ ⟨[], 0⟩ _ (SIndent.zero _) (entryQ_at []) (.nil 0 _)))

open L4YAML.Surface in
/-- The same input split two-then-one, and nil-then-three: the same end position. -/
private lemma tailQ3_2_1 : SCompactMapTail 0 ⟨['?', '\n', '?', '\n', '?', '\n'], 0⟩ ⟨[], 0⟩ :=
  compactMapTail_append_read
    (.cons 0 _ _ ⟨['?', '\n', '?', '\n'], 0⟩ _ (SIndent.zero _) (entryQ_at ['?', '\n', '?', '\n'])
      (.cons 0 _ _ ⟨['?', '\n'], 0⟩ _ (SIndent.zero _) (entryQ_at ['?', '\n']) (.nil 0 _)))
    (.cons 0 _ _ ⟨[], 0⟩ _ (SIndent.zero _) (entryQ_at []) (.nil 0 _))

open L4YAML.Surface in
example : SCompactMapTail 0 ⟨['?', '\n', '?', '\n', '?', '\n'], 0⟩ ⟨[], 0⟩ :=
  compactMapTail_append_read (.nil 0 _) tailQ3_1_2

open L4YAML.Surface in
/-- A concrete tail cannot be appended past the input: the only tail from `⟨[], 0⟩` is `nil`, so the
    appended tail from `?⏎?⏎?⏎` ends at `⟨[], 0⟩` and the two readings above agree there. -/
example : SCompactMapTail 0 ⟨['?', '\n', '?', '\n', '?', '\n'], 0⟩ ⟨[], 0⟩ :=
  compactMapTail_append_read tailQ3_2_1 (.nil 0 ⟨[], 0⟩)

open L4YAML.Proofs.IndentStackCover in
/-- The frame stack of the LAST scanner state on `line` (0-based) while scanning `input` — the
    stack at a named park, not the deepest stack of the scan; `[]` if the scan never stands there. -/
def framesAtLine (input : String) (line : Nat) (fuel : Nat := 64) : List FrameLevel := Id.run do
  let mut s := ScannerState.mk' input
  let mut found : List FrameLevel := []
  for _ in [:fuel] do
    match scanNextToken s with
    | .error _ => return found
    | .ok none => return found
    | .ok (some s') =>
      s := s'
      if s.currentPos.line == line then found := s.indents.toList.map FrameLevel.ofEntry
      else if s.currentPos.line > line then return found
  return found

open ExplicitOnlyMirror L4YAML.Proofs.IndentStackCover in
def testRootFrameSupplyRead (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 71: the (α) root-frame supply, stage B read — the root births hold the root frame; the compact-map tail appends; [211]'s two block/document inputs under the explicit-only reading"
  -- (i) the scanner's stack at the root births (P8), fuel 0/1/2 on the three-key mapping
  -- the stack AT the named state (review of the read item): the last scanner state on a given line,
  -- not the deepest stack of the whole scan — (label, input, line, expected); the birth line of the
  -- root park (line 0) and the sibling's line are read separately.  Predictions: the root mapping's
  -- level stands from the first `:` on, so line 0 already shows `[map 0, map 0]`; `---` resets to
  -- the sentinel `[map 0]` and the next mapping pushes again; `a⏎&x` never pushes.
  let atLine : List (String × String × Nat × List FrameLevel) :=
    [ ("a: 1⏎b: 2 — the park's birth line", "a: 1\nb: 2\n", 0, [FrameLevel.map 0, FrameLevel.map 0]),
      ("a: 1⏎b: 2 — the sibling's line", "a: 1\nb: 2\n", 1, [FrameLevel.map 0, FrameLevel.map 0]),
      ("a: 1⏎b: 2⏎c: 3 — the third line", "a: 1\nb: 2\nc: 3\n", 2, [FrameLevel.map 0, FrameLevel.map 0]),
      ("[a]: 1⏎b: 2 — the flow key's line", "[a]: 1\nb: 2\n", 0, [FrameLevel.map 0, FrameLevel.map 0]),
      ("[a]: 1⏎b: 2 — the sibling's line", "[a]: 1\nb: 2\n", 1, [FrameLevel.map 0, FrameLevel.map 0]),
      ("? a⏎: 1⏎b: 2 — the `?` line", "? a\n: 1\nb: 2\n", 0, [FrameLevel.map 0, FrameLevel.map 0]),
      ("? a⏎: 1⏎b: 2 — the sibling's line", "? a\n: 1\nb: 2\n", 2, [FrameLevel.map 0, FrameLevel.map 0]),
      ("a: 1⏎---⏎b: 2 — the first document's line", "a: 1\n---\nb: 2\n", 0, [FrameLevel.map 0, FrameLevel.map 0]),
      ("a: 1⏎---⏎b: 2 — the `---` line (reset to the sentinel)", "a: 1\n---\nb: 2\n", 1, [FrameLevel.map 0]),
      ("a: 1⏎---⏎b: 2 — the second document's line", "a: 1\n---\nb: 2\n", 2, [FrameLevel.map 0, FrameLevel.map 0]),
      -- REFUTED as predicted `[map 0]`: the plain scalar `a` folds across the break in ONE scanner
      -- step, so no state ever stands on line 0 — the reader returns `[]`; kept as read.
      ("a⏎&x — line 0 (REFUTED: the scalar step crosses the break, no state on the line)", "a\n&x\n", 0, []),
      ("a⏎&x — line 1", "a\n&x\n", 1, [FrameLevel.map 0]),
      ("- a⏎- b — the `-` park's line", "- a\n- b\n", 0, [FrameLevel.map 0, FrameLevel.seq 0]),
      ("- a⏎- b — the second entry's line", "- a\n- b\n", 1, [FrameLevel.map 0, FrameLevel.seq 0]),
      -- the 14546 question (item 461): a flow key at a nested park's own column pushes the MAPPING
      -- level at that column; no `seq n` stands over a `map n` (prediction: `[map 0, map 0, map 2]`
      -- and `[map 0, seq 0, map 2]`)
      ("a:⏎  [b]: 1⏎  c: 2 — the flow key's line", "a:\n  [b]: 1\n  c: 2\n", 1, [FrameLevel.map 0, FrameLevel.map 0, FrameLevel.map 2]),
      ("- [a]: 1⏎  b: 2 — the flow key's line under `-`", "- [a]: 1\n  b: 2\n", 0, [FrameLevel.map 0, FrameLevel.seq 0, FrameLevel.map 2]) ]
  for (label, input, line, expected) in atLine do
    let got := framesAtLine input line
    checkM state s!"rootFrameSupply/at-line {label}: stack [{frameLabel expected}]" (got == expected)
      s!"got [{frameLabel got}]"
  checkFrames state "a: 1⏎b: 2 (root `:` park, one sibling)" "a: 1\nb: 2\n" [FrameLevel.map 0, FrameLevel.map 0]
  checkFrames state "a: 1⏎b: 2⏎c: 3 (two siblings: the tail appends, no new level)" "a: 1\nb: 2\nc: 3\n"
    [FrameLevel.map 0, FrameLevel.map 0]
  checkFrames state "[a]: 1⏎b: 2 (flow key at the root)" "[a]: 1\nb: 2\n" [FrameLevel.map 0, FrameLevel.map 0]
  checkFrames state "? a⏎: 1⏎b: 2 (explicit entry at the root)" "? a\n: 1\nb: 2\n" [FrameLevel.map 0, FrameLevel.map 0]
  checkFrames state "a: 1⏎---⏎b: 2 (explicit document between)" "a: 1\n---\nb: 2\n" [FrameLevel.map 0, FrameLevel.map 0]
  checkFrames state "a⏎&x (no mapping: the sentinel alone)" "a\n&x\n" [FrameLevel.map 0]
  checkFrames state "- a⏎- b (root `-` park)" "- a\n- b\n" [FrameLevel.map 0, FrameLevel.seq 0]
  for (fuel, expected) in [(0, ([] : List FrameLevel)), (1, [FrameLevel.map 0]), (2, [FrameLevel.map 0, FrameLevel.map 0])] do
    let got := deepestFrames "a: 1\nb: 2\nc: 3\n" fuel
    checkM state s!"rootFrameSupply/fuel {fuel}: deepest stack [{frameLabel expected}]" (got == expected)
      s!"got [{frameLabel got}]"
  -- (ii) the parser: (label, input, accepted as (documents, leading scalar, first document's root arity), or refused)
  -- the leading scalar content, through a sequence's or a mapping's first key (Priority 69's reader)
  let rec leadContent : Nat → YamlValue → String
    | _, YamlValue.scalar s => s.content
    | fuel + 1, YamlValue.sequence _ arr _ _ => (arr[0]?.map (leadContent fuel)).getD "<empty sequence>"
    | fuel + 1, YamlValue.mapping _ arr _ _ => (arr[0]?.map (fun p => leadContent fuel p.1)).getD "<empty mapping>"
    | _, _ => "<other>"
  let rootArity (d : YamlDocument) : Nat := match d.value with
    | YamlValue.mapping _ arr _ _ => arr.size
    | YamlValue.sequence _ arr _ _ => arr.size
    | _ => 0
  let rows : List (String × String × Option (Nat × String × Nat)) :=
    [ ("a⏎&x (Refutation 1's input: one bare document, the plain scalar folds)", "a\n&x", some (1, "a &x", 0)),
      ("a: |⏎   x⏎  &x b: *x (Refutation 2's input: the indent-2 line after a mapping at 0 is no sibling)",
        "a: |\n   x\n  &x b: *x", none),
      ("a: 1⏎b: 2⏎c: 3 (three siblings)", "a: 1\nb: 2\nc: 3", some (1, "a", 3)),
      ("[a]: 1⏎b: 2 (flow key, then the sibling)", "[a]: 1\nb: 2", some (1, "a", 2)),
      ("? a⏎: 1⏎b: 2 (explicit entry, then the sibling)", "? a\n: 1\nb: 2", some (1, "a", 2)),
      ("a: 1⏎---⏎b: 2 (two documents, one key each)", "a: 1\n---\nb: 2", some (2, "a", 1)),
      ("a⏎&x⏎...⏎b (`...` then a bare document: two documents)", "a\n&x\n...\nb", some (2, "a &x", 0)),
      ("a⏎---⏎&x b (explicit document carries the anchor)", "a\n---\n&x b", some (2, "a", 0)) ]
  for (label, src, expected) in rows do
    let got : Option (Nat × String × Nat) := match L4YAML.TokenParser.parseYaml src with
      | .ok docs => some (docs.size, (docs[0]?.map (fun d => leadContent 4 d.value)).getD "<no document>",
          (docs[0]?.map rootArity).getD 0)
      | .error _ => none
    checkM state s!"rootFrameSupply/parser {label}" (got == expected) s!"got {repr got}, expected {repr expected}"
  -- (iii) the two document walks (Priority 68's mirror) on the two `TraceOfBlockAmbiguity` inputs.
  -- P6 REFUTED on the second: the broad walk reads 1, not 2 — the mirror counts document starts at
  -- COLUMN 0 only, and Refutation 2's second bare document (`  &x b: *x`) starts at column 2; the
  -- broad grammar admits it at the `TBlockNode` level, below what a line walk can see.  Kept as read.
  for (label, src, eExpl, eBroad) in [("a⏎&x", "a\n&x", 1, 2),
      ("a: |⏎   x⏎  &x b: *x (REFUTED: the walk cannot see an indent-2 bare document)", "a: |\n   x\n  &x b: *x", 1, 1)] do
    let gotE := explicitOnlyDocs src
    let gotB := broadDocs src
    checkM state s!"rootFrameSupply/walk {label}: explicit-only {eExpl}, broad {eBroad}" (gotE == eExpl && gotB == eBroad)
      s!"got {gotE} / {gotB}"

/-- Priority 34 (`[173]` tail confined to EOF): the executable side of
`collectLineContentLoop_fst_nonempty` and of `BlockStopOk.badChar`'s non-empty run
(`lineRunPlus_toBodyTail`).  An `nb-char` first and fuel ≥ 1 give non-empty content; the
hypothesis fails at fuel 0 and on a BOM-first line, and there `collectBlockScalarLoop`'s
non-`nb-char` exit now returns the LINE START (the partial indent is left to the enclosing
collection) instead of the position after the indent. -/
def testBlockScalarTailEof (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 34: [173] partial-indent tail EOF-only — collectLineContentLoop non-emptiness, empty-run exit"
  -- nb-char first, fuel 1/2/5, empty and non-empty accumulator: content non-empty.
  for (label, input) in [("plain", "abc\n"), ("nb-then-bom", "a\uFEFFb"), ("single", "x")] do
    let s := ScannerState.mk' input
    for n in [1, 2, 5] do
      for acc in ["", "pre"] do
        checkM state s!"fst_nonempty/{label}/fuel {n}/acc '{acc}'"
          ((collectLineContentLoop s acc n).1.isEmpty == false) ""
  -- Hypothesis fails: fuel 0 (content stays as given), BOM first, line break first.
  checkM state "fst_nonempty/fuel 0 returns the accumulator unchanged"
    ((collectLineContentLoop (ScannerState.mk' "abc") "" 0).1.isEmpty == true) ""
  checkM state "fst_nonempty/BOM first: empty run"
    ((collectLineContentLoop (ScannerState.mk' "\uFEFFx") "" 3).1.isEmpty == true) ""
  checkM state "fst_nonempty/break first: empty run"
    ((collectLineContentLoop (ScannerState.mk' "\nx") "" 3).1.isEmpty == true) ""
  -- nb-char then BOM: the run stops AT the BOM with one char collected.
  let sb := ScannerState.mk' "a\uFEFFb"
  checkM state "fst_nonempty/nb-then-bom stops at the BOM"
    ((collectLineContentLoop sb "" 5).1 == "a" && (collectLineContentLoop sb "" 5).2.offset == 1) ""
  -- The block-scalar loop at content indent 2: an empty run before a BOM leaves the
  -- scanner at the line start (offset 0); a non-empty run keeps the after-line position.
  let sEmpty := ScannerState.mk' "  \uFEFF"
  let rEmpty := collectBlockScalarLoop sEmpty "" 8 2 sEmpty.inputEnd
  checkM state "badChar/empty run: scanner returns the line start" (rEmpty.2.offset == 0) ""
  checkM state "badChar/empty run: no content collected" (rEmpty.1 == "") ""
  let sRun := ScannerState.mk' "  ab\uFEFF"
  let rRun := collectBlockScalarLoop sRun "" 8 2 sRun.inputEnd
  checkM state "badChar/non-empty run: scanner stops at the BOM" (rRun.2.offset == 4) ""
  checkM state "badChar/non-empty run: content is the run" (rRun.1 == "ab") ""
  -- Parser side: both inputs are refused (dispatch rejects the BOM) — same verdict as before.
  for (label, src) in [("empty run", "a: |\n  \uFEFF"), ("run", "a: |\n  ab\uFEFF")] do
    let refused := match L4YAML.TokenParser.parseYaml src with
      | .ok _ => false
      | .error _ => true
    checkM state s!"badChar/parser refuses ({label})" refused ""

/-- Priority 37 (item 369, lane A of the `[211]` landing): the parser's reading of a key that
lands LEFT of an awaited block entry — `rootMapRoute_or_refused`'s fallback arms key it as a
fresh bare document (`implicitContinue`), the parser reads it as a SIBLING of the enclosing
mapping/sequence (one document, two root entries) or refuses the landing (`trailingContent`).
`some (docs, n)` = accepted with `docs` documents and `n` entries in the first root collection;
`none` = refused.  The rows are item 297's table plus the `...`-closed contrast (two documents,
`suffixContinue`'s own slot). -/
def testRootSiblingLedger (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 37: a key landing left of the awaited entry is a root SIBLING, not a bare document (item 369)"
  let rootArity : YamlValue → Nat
    | .mapping _ arr => arr.size
    | .sequence _ arr => arr.size
    | _ => 0
  let rows : List (String × String × Option (Nat × Nat)) :=
    [ ("? a⏎:⏎b: 1 (explicit `:` park, dedent to col 0)", "? a\n:\nb: 1", some (1, 2)),
      ("? a⏎: v⏎b: 1", "? a\n: v\nb: 1", some (1, 2)),
      ("a: 1⏎b: 2 (plain sibling)", "a: 1\nb: 2", some (1, 2)),
      ("k:⏎  ? a⏎  :⏎  b:⏎d: 3 (item 297 coverless row)", "k:\n  ? a\n  :\n  b:\nd: 3", some (1, 2)),
      ("k:⏎  ? a⏎  :⏎  b:⏎&p d: 3 (run-headed twin)", "k:\n  ? a\n  :\n  b:\n&p d: 3", some (1, 2)),
      ("k:⏎  ? a⏎  :⏎  b:⏎!t d: 3", "k:\n  ? a\n  :\n  b:\n!t d: 3", some (1, 2)),
      ("- ? a⏎  :⏎  b:⏎- c (sequence sibling)", "- ? a\n  :\n  b:\n- c", some (1, 2)),
      ("k:⏎  - ?⏎    b:⏎d: 1", "k:\n  - ?\n    b:\nd: 1", some (1, 2)),
      ("k:⏎  :⏎b: 2 (items 39/40/99's `dedent` input)", "k:\n  :\nb: 2", some (1, 2)),
      ("k:⏎  -⏎b: 2 (empty `-` entry, then a root sibling: the `pendingBlock` landing)", "k:\n  -\nb: 2", some (1, 2)),
      ("k:⏎  - a⏎b: 2", "k:\n  - a\nb: 2", some (1, 2)),
      ("k:⏎  -⏎  ? x⏎b: 2 (`?` landing left of the `-`)", "k:\n  -\n  ? x\nb: 2", none),
      ("k:⏎  -⏎? x (a `?` at the root after an empty `-`)", "k:\n  -\n? x", some (1, 2)),
      ("k:⏎  -⏎: x (a `:` at the root after an empty `-`: `[189]` empty key)", "k:\n  -\n: x", some (1, 2)),
      ("? a⏎:⏎...⏎b: 1 (`...` closes: two documents, suffixContinue's slot)", "? a\n:\n...\nb: 1", some (2, 1)),
      ("k:⏎  a:⏎ b: 2 (covering frames: refused)", "k:\n  a:\n b: 2", none),
      ("k:⏎    a:⏎  b: 2", "k:\n    a:\n  b: 2", none),
      ("- k:⏎    a:⏎   b: 2", "- k:\n    a:\n   b: 2", none),
      ("- a⏎b: 1 (a mapping key after a root sequence: refused)", "- a\nb: 1", none),
      ("- - a⏎b: 1", "- - a\nb: 1", none),
      ("a⏎&x (R1: plain folds, one scalar document)", "a\n&x", some (1, 0)) ]
  for (label, src, expected) in rows do
    let got : Option (Nat × Nat) := match L4YAML.TokenParser.parseYaml src with
      | .ok docs => some (docs.size, (docs[0]?.map (fun d => rootArity d.value)).getD 0)
      | .error _ => none
    checkM state s!"root sibling {label}" (got == expected)
      s!"parseYaml: {repr got} (docs, root arity), expected {repr expected}"

/-- Priority 38 (item 370, lane A proper): a park re-born at a SIBLING `-` (`accum_block_on_pendingBlock`'s
snoc arm) now carries the enclosing frames the first `-` held, so a key that then lands LEFT of the
sequence resumes the enclosing mapping (one document, the key a root sibling) instead of exit (b) of the
key pack (`rootMapRoute_or_refused`'s fresh bare document).  The parser's verdicts: `some (docs, n)` =
accepted with `docs` documents and `n` root entries; `none` = refused.  Dedents to a width the stack
does not hold are refused at preprocessing (`trailingContent`); a key at a root SEQUENCE's own column
is refused at its `:` (§8.2.1). -/
def testSiblingDashFrames (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 38: a key landing left of a sibling `-` resumes the enclosing mapping (item 370)"
  let rootArity : YamlValue → Nat
    | .mapping _ arr => arr.size
    | .sequence _ arr => arr.size
    | _ => 0
  let rows : List (String × String × Option (Nat × Nat)) :=
    [ ("k:⏎  -⏎  -⏎b: 2 (two empty entries, then a root key)", "k:\n  -\n  -\nb: 2", some (1, 2)),
      ("k:⏎  - a⏎  - b⏎c: 2", "k:\n  - a\n  - b\nc: 2", some (1, 2)),
      ("k:⏎  -⏎  -⏎  -⏎b: 2 (three siblings)", "k:\n  -\n  -\n  -\nb: 2", some (1, 2)),
      ("k:⏎  -⏎  - ? x⏎b: 2 (compact `?` in the sibling)", "k:\n  -\n  - ? x\nb: 2", some (1, 2)),
      ("k:⏎  -⏎  -⏎? x (a `?` at the root)", "k:\n  -\n  -\n? x", some (1, 2)),
      ("k:⏎  -⏎  -⏎: x (a `:` at the root: `[189]` empty key)", "k:\n  -\n  -\n: x", some (1, 2)),
      ("- k:⏎    -⏎    -⏎  j: 1 (nested: the key resumes the compact mapping)", "- k:\n    -\n    -\n  j: 1", some (1, 1)),
      ("k:⏎  -⏎  -⏎   b: 2 (deeper: the key is the second entry's node)", "k:\n  -\n  -\n   b: 2", some (1, 1)),
      ("- a⏎-⏎b: 1 (root sequence: refused at the `:`)", "- a\n-\nb: 1", none),
      ("k:⏎  -⏎  -⏎  b: 2 (a key at the sequence's own column: refused)", "k:\n  -\n  -\n  b: 2", none),
      ("k:⏎  -⏎  -⏎ ? x (a width the stack does not hold: refused at preprocessing)", "k:\n  -\n  -\n ? x", none) ]
  for (label, src, expected) in rows do
    let got : Option (Nat × Nat) := match L4YAML.TokenParser.parseYaml src with
      | .ok docs => some (docs.size, (docs[0]?.map (fun d => rootArity d.value)).getD 0)
      | .error _ => none
    checkM state s!"sibling dash frames {label}" (got == expected)
      s!"parseYaml: {repr got} (docs, root arity), expected {repr expected}"

/-- Priority 39 (item 371, the framed value-line pack): every value-line pack now ends in
`ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v` instead of the fused
`SLYamlStream sp_start sp_v`, so after the explicit `:`'s value the mapping at `nv` goes on with its
SIBLINGS — `? a⏎:⏎b: 1` is one document with two root entries, where the fused pack could only
close the mapping (item 370's frameless exit (b)).  `some (docs, n)` = accepted with `docs` documents
and `n` entries at the root; `none` = refused.  The enclosing-frames row (`x:⏎  ? a⏎  :⏎y: 2`) is the
parser's verdict only — the pack carries ONE level, the enclosing ones are not paid by this item. -/
def testValueLineResume (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 39: the explicit `:`'s value resumes its mapping — siblings after `? a⏎:` (item 371)"
  let rootArity : YamlValue → Nat
    | .mapping _ arr => arr.size
    | .sequence _ arr => arr.size
    | _ => 0
  let rows : List (String × String × Option (Nat × Nat)) :=
    [ ("? a⏎:⏎b: 1 (empty explicit value, then a sibling)", "? a\n:\nb: 1", some (1, 2)),
      ("? a⏎: b⏎c: 1 (inline explicit value, then a sibling)", "? a\n: b\nc: 1", some (1, 2)),
      ("?⏎:⏎b: 1 (empty key and value)", "?\n:\nb: 1", some (1, 2)),
      ("? - a⏎:⏎b: 1 (compact sequence key)", "? - a\n:\nb: 1", some (1, 2)),
      ("? [a]⏎:⏎b: 1 (flow key)", "? [a]\n:\nb: 1", some (1, 2)),
      ("? a⏎: b⏎? c⏎: d (two explicit entries)", "? a\n: b\n? c\n: d", some (1, 2)),
      ("? a⏎:⏎  b: 1 (the value is a nested mapping)", "? a\n:\n  b: 1", some (1, 1)),
      ("? a⏎:⏎ b: 1 (one column in: still the value)", "? a\n:\n b: 1", some (1, 1)),
      ("x:⏎  ? a⏎  :⏎  b: 1 (nested: the sibling resumes the inner mapping)", "x:\n  ? a\n  :\n  b: 1", some (1, 1)),
      ("x:⏎  ? a⏎  :⏎y: 2 (enclosing level: parser verdict, not paid here)", "x:\n  ? a\n  :\ny: 2", some (1, 2)),
      -- Rule 2 refuted the row as first written (expected refused): `[185]` lets a block
      -- sequence value stand at the mapping's own column (`seq-spaces(n, block-out) = n-1`),
      -- so the `-` is the explicit `:`'s VALUE — `{a: [b]}`, one entry.
      ("? a⏎:⏎- b (a `-` at the mapping's own column is the VALUE: `{a: [b]}`)", "? a\n:\n- b", some (1, 1)),
      ("? a⏎:⏎b (a plain scalar at the root after the entry: refused)", "? a\n:\nb", none) ]
  for (label, src, expected) in rows do
    let got : Option (Nat × Nat) := match L4YAML.TokenParser.parseYaml src with
      | .ok docs => some (docs.size, (docs[0]?.map (fun d => rootArity d.value)).getD 0)
      | .error _ => none
    checkM state s!"value-line resume {label}" (got == expected)
      s!"parseYaml: {repr got} (docs, root arity), expected {repr expected}"

/-- Priority 40 (item 372): a key LANDING ON A SEQUENCE TOP is refused at its `:`
    (§8.2.1 `trailingContent`), and that refusal is the only survivor of the key
    pack's `w ∉ ks` exit under a cover — the `SeqTopKey` face the `:` consumer
    refutes.  Neighbours that are accepted name the other exits: a `-` sibling
    (the landing is a sequence entry, not a key), a key resuming an OPEN mapping
    level (a frame), a key inside the entry's own mapping. -/
def testSeqTopKeyFace (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 40: a key on a sequence top is refused at its `:` — the key pack's SeqTopKey face (item 372)"
  let rootArity : YamlValue → Nat
    | .mapping _ arr => arr.size
    | .sequence _ arr => arr.size
    | _ => 0
  let rows : List (String × String × Option (Nat × Nat)) :=
    [ ("- a⏎b: 1 (key at the root sequence's column: refused at the `:`)", "- a\nb: 1", none),
      ("k:⏎  - a⏎  b: 1 (key at a nested sequence's column: refused)", "k:\n  - a\n  b: 1", none),
      ("- - a⏎  b: 1 (key at an inner sequence's column: refused)", "- - a\n  b: 1", none),
      ("- a⏎\"b\": 1 (quoted key at the sequence's column: refused)", "- a\n\"b\": 1", none),
      ("- a⏎&p b: 1 (props-headed key at the sequence's column: refused — PRICED, props lane)", "- a\n&p b: 1", none),
      ("- a⏎- b (a `-` sibling, not a key: accepted)", "- a\n- b", some (1, 2)),
      ("k:⏎  - a⏎b: 1 (the key resumes the OPEN root mapping — a frame, not a sequence top)", "k:\n  - a\nb: 1", some (1, 2)),
      ("- a: 1⏎  b: 2 (a key inside the entry's own mapping)", "- a: 1\n  b: 2", some (1, 1)),
      ("- a⏎  b: 1 (one column in: the plain scalar folds, then `:` is refused)", "- a\n  b: 1", none),
      ("-⏎b: 1 (empty entry, then a key at the sequence's column: refused)", "-\nb: 1", none) ]
  for (label, src, expected) in rows do
    let got : Option (Nat × Nat) := match L4YAML.TokenParser.parseYaml src with
      | .ok docs => some (docs.size, (docs[0]?.map (fun d => rootArity d.value)).getD 0)
      | .error _ => none
    checkM state s!"seq-top key face {label}" (got == expected)
      s!"parseYaml: {repr got} (docs, root arity), expected {repr expected}"

/-- The states at which preprocessing hands a `:` to the block dispatcher while scanning
    `input` (the lemma's `s`, before the directive reset).  Not `colonStates`: that reads the
    raw cursor, which never rests on the explicit `:` of `? a⏎: b` (it sits behind a break). -/
def colonDispatchStates (input : String) (fuel : Nat := 64) : List ScannerState := Id.run do
  let mut s := ScannerState.mk' input
  let mut acc : List ScannerState := []
  for _ in [:fuel] do
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) => if c == ':' then acc := acc ++ [sp]
    | _ => break
    match scanNextToken s with
    | .ok (some s') => s := s'
    | _ => break
  return acc

/-- Item 372's lemma at one `:` pause (after the directive reset the producers dispatch
    over): `(premises, face, dispatched)` — the four side premises of
    `seqTopKey_refuted_at_colon` read off the state, `SeqTopKey` as a Bool, and whether
    `scanNextToken_dispatchBlockIndicators` dispatched.  The lemma says: premises ∧
    dispatched → ¬ face. -/
def seqTopKeyRow (sp : ScannerState) : Bool × Bool × Bool :=
  let sd := if sp.allowDirectives then
    { sp with allowDirectives := false, documentEverStarted := true } else sp
  let prem := !sd.inFlow && sd.simpleKey.possible && sd.simpleKey.pos.offset != sd.offset
    && sd.simpleKey.pos.line == sd.line
  let face := (sd.indents.back?.map fun e =>
    e.isSequence && e.column == (sd.simpleKey.pos.col : Int)) == some true
  let disp := match scanNextToken_dispatchBlockIndicators sd ':' with
    | .ok (some _) => true
    | _ => false
  (prem, face, disp)

/-- The `:` pauses of `input`, classified: `holds` (premises, dispatched, no face),
    `facedRefused` (premises, face, NOT dispatched — the scanner's side of the lemma),
    `sidePremise` / `inFlow` (a side premise fails — for the explicit `:` of `? a⏎: b` it is
    `h_behind`: a fresh simple key is saved AT the `:`), `refuted` (premises, dispatched,
    face). -/
def seqTopKeyLemmaWalk (input : String) : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut holds := 0
  let mut facedRefused := 0
  let mut sidePremise := 0
  let mut inFlow := 0
  let mut refuted := 0
  for sp in colonDispatchStates input do
    let (prem, face, disp) := seqTopKeyRow sp
    if prem && disp && !face then holds := holds + 1
    else if prem && face && !disp then facedRefused := facedRefused + 1
    else if prem && disp && face then refuted := refuted + 1
    else if sp.inFlow then inFlow := inFlow + 1
    else sidePremise := sidePremise + 1
  return (holds, facedRefused, sidePremise, inFlow, refuted)

def testSeqTopKeyLemma (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 40b: seqTopKey_refuted_at_colon and SeqTopKey.of_eq on the scanner's own `:` states (item 372, PR review)"
  -- (holds, facedRefused, sidePremise, inFlow, refuted); `refuted` must be 0 everywhere.
  let rows : List (String × String × (Nat × Nat × Nat × Nat × Nat)) :=
    [ ("a: 1 (root key, sentinel stack)", "a: 1", (1, 0, 0, 0, 0)),
      ("a: 1⏎b: 2 (two root keys)", "a: 1\nb: 2", (2, 0, 0, 0, 0)),
      ("k:⏎  a: 1 (mapping top at the key's column)", "k:\n  a: 1", (2, 0, 0, 0, 0)),
      ("- a: 1 (key inside the entry: mapping over the sequence)", "- a: 1", (1, 0, 0, 0, 0)),
      ("- a: 1⏎  b: 2 (Priority 40's accepted neighbour)", "- a: 1\n  b: 2", (2, 0, 0, 0, 0)),
      ("k:⏎  - a⏎b: 1 (the dedent popped the sequence: holds)", "k:\n  - a\nb: 1", (2, 0, 0, 0, 0)),
      ("- a⏎b: 1 (the item's input: face holds, `:` refused)", "- a\nb: 1", (0, 1, 0, 0, 0)),
      ("-⏎b: 1 (empty entry, then the face)", "-\nb: 1", (0, 1, 0, 0, 0)),
      ("k:⏎  - a⏎  b: 1 (nested sequence top)", "k:\n  - a\n  b: 1", (1, 1, 0, 0, 0)),
      ("- - a⏎  b: 1 (inner sequence top)", "- - a\n  b: 1", (0, 1, 0, 0, 0)),
      ("- a⏎\"b\": 1 (quoted key on the sequence top)", "- a\n\"b\": 1", (0, 1, 0, 0, 0)),
      ("- a⏎  b: 1 (one column in: the fold makes a multiline key)", "- a\n  b: 1", (0, 0, 1, 0, 0)),
      ("? a⏎: b (explicit `:`: the saved key sits AT the `:` — h_behind fails)", "? a\n: b", (0, 0, 1, 0, 0)),
      ("{a: b} (flow `:`)", "{a: b}", (0, 0, 0, 1, 0)),
      ("[a: 1] (flow pair `:`)", "[a: 1]", (0, 0, 0, 1, 0)) ]
  for (label, src, expected) in rows do
    let got := seqTopKeyLemmaWalk src
    let detail := (colonDispatchStates src).map seqTopKeyRow
    checkM state s!"seq-top lemma {label}" (got == expected)
      s!"(holds, facedRefused, sidePremise, inFlow, refuted) = {repr got}, expected {repr expected}; rows (prem, face, disp) = {repr detail}"
  -- `SeqTopKey.of_eq`'s reading at the executable level: the face is a function of
  -- `indents` and the key's column only — rewriting every other field keeps it.
  let faceOf (s : ScannerState) : Bool := (seqTopKeyRow s).2.1
  for (label, src) in [("- a⏎b: 1", "- a\nb: 1"), ("k:⏎  - a⏎  b: 1", "k:\n  - a\n  b: 1")] do
    match (colonDispatchStates src).getLast? with
    | some sp =>
      let moved : ScannerState := { sp with
        offset := sp.offset + 7
        line := sp.line + 1
        col := sp.col + 3
        tokens := #[]
        simpleKeyAllowed := !sp.simpleKeyAllowed
        simpleKey := { sp.simpleKey with
          pos := { sp.simpleKey.pos with offset := 0, line := 99 } } }
      let colMoved : ScannerState := { sp with
        simpleKey := { sp.simpleKey with
          pos := { sp.simpleKey.pos with col := sp.simpleKey.pos.col + 1 } } }
      let popped : ScannerState := { sp with indents := sp.indents.pop }
      checkM state s!"of_eq {label}: face at the pause" (faceOf sp) s!"face={faceOf sp}"
      checkM state s!"of_eq {label}: rides a step keeping indents and the key column" (faceOf moved)
        s!"face={faceOf moved}"
      checkM state s!"of_eq {label}: the key column is load-bearing" (!faceOf colMoved)
        s!"face={faceOf colMoved}"
      checkM state s!"of_eq {label}: the stack is load-bearing" (!faceOf popped)
        s!"face={faceOf popped}"
    | none => checkM state s!"of_eq {label}: a `:` pause exists" false "no pause"

/-- Item 373's reading of the `_or_refused` wrappers' discriminator at one dispatcher-bound
    landing: `(open, seqTop)` — `h_op` (`s_prep.indents.any (column == col)`, the sibling arm)
    and whether the stack's top is a SEQUENCE at the landing column (item 372's face). -/
def siblingArmRow (sp : ScannerState) : Bool × Bool :=
  let sd := if sp.allowDirectives then
    { sp with allowDirectives := false, documentEverStarted := true } else sp
  let op := sd.indents.any fun e => e.column == (sd.col : Int)
  let seqTop := (sd.indents.back?.map fun e => e.isSequence && e.column == (sd.col : Int)) == some true
  (op, seqTop)

/-- Every landing `scanNextToken_preprocess` hands the block dispatcher while scanning `input`
    (any character), classified by the wrappers' DISCRIMINATOR: `(openMap, seqTop, closed)` =
    landings on an open mapping level, on a sequence top, at no open level.  These are scanner
    landings, not wrapper reachability — most are routed before any `_or_refused` wrapper is
    applied; the rows say where the sibling arm's `h_op` can be true at all. -/
def siblingArmWalk (input : String) (fuel : Nat := 64) : Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut openMap := 0
  let mut seqTop := 0
  let mut closed := 0
  for _ in [:fuel] do
    match scanNextToken_preprocess s with
    | .ok (some (sp, _)) =>
      if sp.line != s.line then
        let (op, st) := siblingArmRow sp
        if st then seqTop := seqTop + 1
        else if op then openMap := openMap + 1
        else closed := closed + 1
    | _ => break
    match scanNextToken s with
    | .ok (some s') => s := s'
    | _ => break
  return (openMap, seqTop, closed)

def testSiblingArmDomain (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 41: the `_or_refused` wrappers' sibling arm (h_op = true) — what lands on an open level, and the parser's verdict (item 373)"
  -- (openMap, seqTop, closed) over every dispatcher-bound landing, and whether parseYaml accepts.
  -- REFUTED as first written (every landing of a line with an open level counted as `open`):
  -- `h_op` holds at exactly ONE landing per sibling line — the line-start one — and every
  -- mid-line token (`:`, the value) lands at no level's column, where the wrappers are
  -- never reached.  The sibling arm's whole domain is the line-start landing.
  let rows : List (String × String × (Nat × Nat × Nat) × Bool) :=
    [ ("a: 1 (one root key: every landing is at the root level)", "a: 1", (0, 0, 0), true),
      ("a: 1⏎b: 2 (the sibling key resumes the root mapping)", "a: 1\nb: 2", (1, 0, 0), true),
      ("k:⏎  a: 1⏎  b: 2 (nested sibling)", "k:\n  a: 1\n  b: 2", (1, 0, 1), true),
      ("a: 1⏎&p b: 2 (props-headed sibling: content lane)", "a: 1\n&p b: 2", (1, 0, 0), true),
      ("a: 1⏎[1]: b (flow-key sibling)", "a: 1\n[1]: b", (1, 0, 0), true),
      ("- a⏎b: 1 (sequence top at the landing: item 372's face)", "- a\nb: 1", (0, 1, 0), false),
      ("k:⏎  - a⏎  b: 1 (nested sequence top)", "k:\n  - a\n  b: 1", (0, 1, 1), false),
      ("- a⏎- b (the `-` sibling lands on the sequence top and is accepted)", "- a\n- b", (0, 1, 0), true),
      ("a: 1⏎  b: 2 (REFUTED (0, 0, 1): preprocessing refuses the indent before any landing is handed over — no row)", "a: 1\n  b: 2", (0, 0, 0), false),
      ("a: 1⏎...⏎b: 2 (post-`...`: the sibling is a new document, not a resume)", "a: 1\n...\nb: 2", (1, 0, 1), true) ]
  for (label, src, expected, accepted) in rows do
    let got := siblingArmWalk src
    let ok := match L4YAML.TokenParser.parseYaml src with | .ok _ => true | .error _ => false
    checkM state s!"sibling arm {label}" (got == expected && ok == accepted)
      s!"(openMap, seqTop, closed) = {repr got} accepted={ok}; expected {repr expected} accepted={accepted}"

/-- **Priority 42 (item 374): the sequence-top face RIDES `ResumeKeyCtx`.**  Over the
    break-crossing landings of `input` (the only ones `resumectx_of_landing` is built from),
    `(face, level, closed)` = landings on a sequence top at the landing column (item 374's new
    disjunct — the frames named no level there, so the context used to decline), landings on an
    open NON-sequence level (the resume), landings at no level.  Scanner landings, read with the
    context's own discriminators; reachability is the parser's verdict beside them. -/
def seqTopResumeWalk (input : String) (fuel : Nat := 64) : Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut face := 0
  let mut level := 0
  let mut closed := 0
  for _ in [:fuel] do
    match scanNextToken_preprocess s with
    | .ok (some (sp, _)) =>
      if sp.line != s.line then
        let (op, st) := siblingArmRow sp
        if st then face := face + 1
        else if op then level := level + 1
        else closed := closed + 1
    | _ => break
    match scanNextToken s with
    | .ok (some s') => s := s'
    | _ => break
  return (face, level, closed)

def testSeqTopResumeCtx (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 42: item 374 — the sequence-top face on ResumeKeyCtx: where the declined resume lands on a sequence top, and the parser's verdict"
  -- (face, level, closed) over the break-crossing landings; every face row with a `:` key is
  -- REFUSED (the `:` consumers refute `SeqTopKey`), every level row resumes and is accepted.
  let rows : List (String × String × (Nat × Nat × Nat) × Bool) :=
    [ ("- a⏎b: 1 (root sequence top: the face, refused at the `:`)", "- a\nb: 1", (1, 0, 0), false),
      ("k:⏎  - a⏎  b: 1 (nested sequence top under a mapping: pendingBlock park)", "k:\n  - a\n  b: 1", (1, 0, 1), false),
      ("- - a⏎  b: 1 (sequence top under a sequence)", "- - a\n  b: 1", (1, 0, 0), false),
      ("? a⏎:⏎  - x⏎  b: 1 (sequence top under an explicit value: pendingMapValue park; REFUTED (1, 0, 2): the `:` line-start lands on the open mapping level, a `level` landing)", "? a\n:\n  - x\n  b: 1", (1, 1, 1), false),
      ("- a⏎- b (the `-` sibling on the sequence top is an ENTRY, accepted)", "- a\n- b", (1, 0, 0), true),
      ("k:⏎  -⏎  -⏎b: 2 (item 370: the dedent key resumes `k`'s level; REFUTED (0, 1, 2): the sibling `-` lands on the sequence top — a face landing that is an ENTRY, not a key)", "k:\n  -\n  -\nb: 2", (1, 1, 1), true),
      ("k:⏎  a: 1⏎  b: 2 (the frames name the level: resume)", "k:\n  a: 1\n  b: 2", (0, 1, 1), true),
      ("a: 1⏎b: 2 (root resume)", "a: 1\nb: 2", (0, 1, 0), true),
      ("- a⏎b (plain scalar on the sequence top, no key: not the face's consumer)", "- a\nb", (1, 0, 0), false),
      ("k:⏎  - a⏎b: 1 (dedent past the sequence to the root mapping: resume, not the face)", "k:\n  - a\nb: 1", (0, 1, 1), true) ]
  for (label, src, expected, accepted) in rows do
    let got := seqTopResumeWalk src
    let ok := match L4YAML.TokenParser.parseYaml src with | .ok _ => true | .error _ => false
    checkM state s!"seqtop resume {label}" (got == expected && ok == accepted)
      s!"(face, level, closed) = {repr got} accepted={ok}; expected {repr expected} accepted={accepted}"

/-- **Priority 43 (item 375): the openers' sibling landings are ACCEPTED, so the `[211]` flip
    cannot REFUTE them.**  Each row lands a `:`/`?`/flow opener's park and then a sibling key at
    an OPEN level of the park's stack (`h_op = true` at the wrapper); `(openMap, seqTop, closed)`
    over the break-crossing landings, and the parser's verdict beside it.  What this reads:
    scanner landings and verdicts — an accepted row shows the fallback arm, IF reached, has no
    refutation.  What it does NOT read (PR #139's review): which arm the opener's PROOF takes —
    proof irrelevance (§7) makes that unobservable from outside (read off the proof TERMS
    instead by `Tests/Guards/Proofs/OpenerFallbackReach.lean`: per caller path, how each
    optional context of the five openers settles), and the frames lane
    (`h_res_land`) is a proof-side list, not a scanner projection.  `openerLaneRow` reads the
    four lanes that ARE scanner projections at the sibling landing — open level, document
    started (the `h_nodoc` lane is dead), marker line (`h_mk` dead), props run (`h_pr` dead) —
    so the only lane that can keep the arm from its fallback is the frames lane; the sites whose
    producers hand it `Or.inr trivial` reach the fallback by construction (roster in DOCS item
    375's review follow-up).  The reachability of the seven sites by ELABORATION is the stage-1
    flip's reading (`scripts/flip_211_stage1.py`: the wrapper's `∨ True` result does not fit the
    park's route field at exactly those lines). -/
def openerLaneRow (input : String) (fuel : Nat := 64) : Nat × Nat × Nat × Nat := Id.run do
  -- over the break-crossing landings: (open-level landings, of which: document already
  -- started, on a `---` line, at a props run (`&`/`!`))
  let mut s := ScannerState.mk' input
  let mut op := 0; let mut started := 0; let mut marker := 0; let mut props := 0
  for _ in [:fuel] do
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      if sp.line != s.line then
        let (o, st) := siblingArmRow sp
        if o && !st then
          op := op + 1
          let sd := if sp.allowDirectives then
            { sp with allowDirectives := false, documentEverStarted := true } else sp
          if sd.documentEverStarted then started := started + 1
          if sd.docStartLine == some sd.line then marker := marker + 1
          if c == '&' || c == '!' then props := props + 1
    | _ => break
    match scanNextToken s with
    | .ok (some s') => s := s'
    | _ => break
  return (op, started, marker, props)

def testOpenerSiblingAccepted (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 43: item 375 — the openers' sibling landings parse (unrefutable); the scanner-visible lanes decline there, only the frames lane is left"
  let rows : List (String × String × (Nat × Nat × Nat) × Bool) :=
    [ ("a: 1⏎b: 2 (`:` opener, root sibling)", "a: 1\nb: 2", (1, 0, 0), true),
      ("a:⏎  x: 1⏎b: 2 (`:` opener with a nested value, dedent sibling)", "a:\n  x: 1\nb: 2", (1, 0, 1), true),
      ("? a⏎: 1⏎b: 2 (`?` opener, sibling after the explicit value; REFUTED (1, 0, 1): the explicit `:` line-start is itself an open-level landing)", "? a\n: 1\nb: 2", (2, 0, 0), true),
      ("? a⏎b: 2 (`?` opener, sibling with the value empty)", "? a\nb: 2", (1, 0, 0), true),
      ("a: [1, 2]⏎b: 2 (flow value then a block sibling: accum_flow_open_depth0's arm)", "a: [1, 2]\nb: 2", (1, 0, 0), true),
      ("a: {x: 1}⏎b: 2 (flow mapping value then a block sibling)", "a: {x: 1}\nb: 2", (1, 0, 0), true),
      ("[1]: a⏎b: 2 (flow key at the root then a sibling: flowKeyRoute_of_root)", "[1]: a\nb: 2", (1, 0, 0), true),
      ("k:⏎  a: 1⏎  b: 2⏎c: 3 (closeThenBlock: dedent past a closed level to a root sibling)", "k:\n  a: 1\n  b: 2\nc: 3", (2, 0, 1), true),
      ("- a: 1⏎  b: 2 (compact mapping in a sequence entry, sibling at the entry's level)", "- a: 1\n  b: 2", (1, 0, 0), true),
      ("- a⏎b: 1 (sequence top, not an opener's sibling: the face, refused)", "- a\nb: 1", (0, 1, 0), false) ]
  for (label, src, expected, accepted) in rows do
    let got := siblingArmWalk src
    let ok := match L4YAML.TokenParser.parseYaml src with | .ok _ => true | .error _ => false
    checkM state s!"opener sibling {label}" (got == expected && ok == accepted)
      s!"(openMap, seqTop, closed) = {repr got} accepted={ok}; expected {repr expected} accepted={accepted}"
  -- the lanes at the open-level landings: every one has a document started (nodoc dead), none
  -- is a `---` line (marker dead), and only the `&p` row is a props run (props dead elsewhere)
  let lanes : List (String × String × (Nat × Nat × Nat × Nat)) :=
    [ ("a: 1⏎b: 2", "a: 1\nb: 2", (1, 1, 0, 0)),
      ("a:⏎  x: 1⏎b: 2", "a:\n  x: 1\nb: 2", (1, 1, 0, 0)),
      ("? a⏎: 1⏎b: 2", "? a\n: 1\nb: 2", (2, 2, 0, 0)),
      ("a: [1, 2]⏎b: 2", "a: [1, 2]\nb: 2", (1, 1, 0, 0)),
      ("[1]: a⏎b: 2", "[1]: a\nb: 2", (1, 1, 0, 0)),
      ("k:⏎  a: 1⏎  b: 2⏎c: 3", "k:\n  a: 1\n  b: 2\nc: 3", (2, 2, 0, 0)),
      ("a: 1⏎&p b: 2 (the props lane, alive only here)", "a: 1\n&p b: 2", (1, 1, 0, 1)),
      ("a: 1⏎---⏎b: 2 (REFUTED (1, 1, 1, 0): the `---` line is never an open-level landing, so the marker lane is read at NO sibling landing; the one open landing is `b` in the restarted document)", "a: 1\n---\nb: 2", (1, 1, 0, 0)) ]
  for (label, src, expected) in lanes do
    let got := openerLaneRow src
    checkM state s!"opener lanes {label}" (got == expected)
      s!"(open, started, marker, props) = {repr got}; expected {repr expected}"

/-- One line-start pause of the scanner, read for item 377 (Priority 45): the character the dispatcher is
    about to see, whether the cursor stands at a block sequence's own indent
    (`atSequenceIndent` — the CURSOR twin of `SeqTopKey`, which reads the SAVED key), and,
    for a `:`/`?` indicator, whether `scanNextToken_dispatchBlockIndicators` accepts it on
    the directives-adjusted state (`seqTopKeyRow`'s `sd`). -/
def openerSeqTopRow (sp : ScannerState) (c : Char) : Bool × Bool × Option Bool :=
  let sd := if sp.allowDirectives then
    { sp with allowDirectives := false, documentEverStarted := true } else sp
  let ind := c == ':' || c == '?'
  let disp := if ind then some (match scanNextToken_dispatchBlockIndicators sd c with
    | .ok (some _) => true
    | _ => false) else none
  (ind, atSequenceIndent sd, disp)

/-- Over the line-start pauses of `input` (as `siblingArmWalk`): `(indSeqTopRefused,
    indSeqTopOk, indClear, otherSeqTop)` — indicators on a sequence top refused / accepted by
    the dispatcher, indicators not on a sequence top, and non-indicator landings on a
    sequence top (the content lane's face, item 372).  Item 377's claim is `indSeqTopOk = 0`
    everywhere: an opener on a sequence top is refused by the dispatcher itself
    (`scanKeyValidateIx`/`scanValueValidateIx`'s `atSequenceIndentIx` check), with no saved
    key in play. -/
def openerSeqTopWalk (input : String) (fuel : Nat := 64) : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut refused := 0
  let mut ok := 0
  let mut clear := 0
  let mut other := 0
  let mut visited := 0
  for _ in [:fuel] do
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      if sp.line != s.line then
        visited := visited + 1
        match openerSeqTopRow sp c with
        | (true, true, some false) => refused := refused + 1
        | (true, true, some true) => ok := ok + 1
        | (true, false, _) => clear := clear + 1
        | (false, true, _) => other := other + 1
        | _ => pure ()
    | _ => break
    match scanNextToken s with
    | .ok (some s') => s := s'
    | _ => break
  return (refused, ok, clear, other, visited)

/-- The lines of `input` after the first whose first non-blank character is `:` or `?` — the
    indicator positions the walker SHOULD reach if nothing before them is refused. -/
def indicatorLineStarts (input : String) : Nat :=
  ((input.splitOn "\n").drop 1).foldl (fun n l =>
    match (l.toList.dropWhile (· == ' ')).head? with | some ':' | some '?' => n + 1 | _ => n) 0

def testOpenerSeqTopRefused (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 45: item 377 — an opener (`:`/`?`) standing at a block sequence's own indent is refused by the dispatcher (atSequenceIndent), so the openers' h_res_land sequence-top branch is refutable without a saved key; the parser's verdict beside it"
  -- (indSeqTopRefused, indSeqTopOk, indClear, otherSeqTop) over the line-start pauses, and
  -- whether parseYaml accepts.  `indSeqTopOk` must be 0 on every row.
  let rows : List (String × String × (Nat × Nat × Nat × Nat × Nat) × Bool) :=
    [ ("- a⏎: b (`:` at the root sequence's indent)", "- a\n: b", (1, 0, 0, 0, 1), false),
      ("- a⏎? b (`?` at the root sequence's indent)", "- a\n? b", (1, 0, 0, 0, 1), false),
      ("- a⏎- b⏎: c (`:` after two entries; REFUTED (1, 0, 0, 0): the second `-` is itself a non-indicator landing on the sequence top)", "- a\n- b\n: c", (1, 0, 0, 1, 2), false),
      ("- a⏎: (empty explicit value at the sequence's indent)", "- a\n:", (1, 0, 0, 0, 1), false),
      ("-⏎: b (empty entry, then `:`)", "-\n: b", (1, 0, 0, 0, 1), false),
      ("- - a⏎  : b (nested sequence's indent)", "- - a\n  : b", (1, 0, 0, 0, 1), false),
      ("k:⏎  - a⏎  : b (nested sequence inside a mapping; REFUTED (0, 0, 0, 0): preprocessing accepts the landing, the DISPATCHER refuses it)", "k:\n  - a\n  : b", (1, 0, 0, 0, 2), false),
      ("k:⏎  - a⏎: b (`:` at the enclosing mapping's indent, not the sequence's: accepted)", "k:\n  - a\n: b", (0, 0, 1, 0, 2), true),
      ("? a⏎: b⏎c: d (`:` after an explicit key: accepted)", "? a\n: b\nc: d", (0, 0, 1, 0, 2), true),
      ("- a⏎b: 1 (content lane: a key on the sequence top — not an opener, refused at its `:`)", "- a\nb: 1", (0, 0, 0, 1, 1), false),
      ("- a⏎? b⏎: c (explicit pair at the sequence's indent; the refused `?` ends the walk: 1 of 2 indicator lines visited — the scope point)", "- a\n? b\n: c", (1, 0, 0, 0, 1), false),
      ("a:⏎- b⏎: c (REFUTED (1, 0, 0, 0) refused: a sequence at its parent mapping's indent pushes no indent level, so the `:` stands on the MAPPING top — clear, and accepted as an empty key)", "a:\n- b\n: c", (0, 0, 1, 0, 2), true) ]
  for (label, src, expected, accepted) in rows do
    let got := openerSeqTopWalk src
    let ok := match L4YAML.TokenParser.parseYaml src with | .ok _ => true | .error _ => false
    checkM state s!"opener on a sequence top {label}" (got == expected && ok == accepted && got.2.1 == 0)
      s!"(indSeqTopRefused, indSeqTopOk, indClear, otherSeqTop, visited) = {repr got} of {indicatorLineStarts src} indicator line(s) accepted={ok}; expected {repr expected} accepted={accepted}"

/-- One ACCEPTED indicator pause, read for item 378 (Priority 46) on the directives-adjusted
    state `sd`: the executable twins of the facts the builders' payment rests on, and the
    survival disjunct the `:` needs.  `keepOk`: `scanValueClearKey_keep` — a key that survives
    the clear is the saved key; `dispOk`: `atSequenceIndent_disp` — the reset twin keeps the
    cursor face; `leOk`: a POPPED landing (the indent stack changed across the break) has
    `col ≤ currentIndent`; `seqOk`: the accepted indicator is not on a sequence top
    (`seqTop_refuted_at_indicator`'s conclusion).  `surv` classifies the `:`'s `h_surv`:
    0 = dead register (`explicitKeyLine = none`, paid), 1 = live register and the key survives
    the clear (paid), 2 = the register clears the key (the DECLINED residue), 3 = a `?` (no
    survival needed). -/
def cursorFaceRow (s sp sd : ScannerState) (c : Char) : Bool × Bool × Bool × Bool × Nat :=
  let cl := scanValueClearKey sd
  let keepOk := !cl.simpleKey.possible || cl.simpleKey == sd.simpleKey
  let dispOk := atSequenceIndent sd == atSequenceIndent sp
  let shape : ScannerState → Array (Int × Bool) := fun st => st.indents.map fun e => (e.column, e.isSequence)
  let leOk := shape sp == shape s || (sp.col : Int) ≤ sp.currentIndent
  let seqOk := !atSequenceIndent sd
  let surv := if c == '?' then 3 else if sd.explicitKeyLine.isNone then 0
    else if cl.simpleKey.possible then 1 else 2
  (keepOk, dispOk, leOk, seqOk, surv)

/-- Over the line-start pauses of `input` at which the dispatcher ACCEPTS a `:`/`?` (the builders'
    domain, `h_dispatch = .ok (some _)`): `(viol, ekNone, survive, cleared, quest)` — rows where
    any of `keepOk`/`dispOk`/`leOk`/`seqOk` fails (must be 0), and the `surv` classes.  A refused
    indicator ends the walk, as in `openerSeqTopWalk`. -/
def cursorFaceWalk (input : String) (fuel : Nat := 64) : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut viol := 0
  let mut ekNone := 0
  let mut survive := 0
  let mut cleared := 0
  let mut quest := 0
  for _ in [:fuel] do
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      if sp.line != s.line && (c == ':' || c == '?') then
        let sd := if sp.allowDirectives then
          { sp with allowDirectives := false, documentEverStarted := true } else sp
        match scanNextToken_dispatchBlockIndicators sd c with
        | .ok (some _) =>
          let (k, d, l, q, sv) := cursorFaceRow s sp sd c
          if !(k && d && l && q) then viol := viol + 1
          match sv with
          | 0 => ekNone := ekNone + 1
          | 1 => survive := survive + 1
          | 2 => cleared := cleared + 1
          | _ => quest := quest + 1
        | _ => pure ()
    | _ => break
    match scanNextToken s with
    | .ok (some s') => s := s'
    | _ => break
  return (viol, ekNone, survive, cleared, quest)

/-- Item 378 (PR #144 review): the premises of `seqTop_refuted_at_indicator` read at every
    accepted `:`/`?` pause — `h_pop` (the landing popped), `h_noflow`, `h_key` (saved key at the
    cursor), `h_poss`, `h_surv` — so the lemma's domain is told apart from the observations outside
    it: `(inScope, inViol, outside, outViol)`, the refutation `atSequenceIndent = false` read on both. -/
def cursorFaceScopeWalk (input : String) (fuel : Nat := 64) : Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut inScope := 0
  let mut inViol := 0
  let mut outside := 0
  let mut outViol := 0
  let shape : ScannerState → Array (Int × Bool) := fun st => st.indents.map fun e => (e.column, e.isSequence)
  for _ in [:fuel] do
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      if c == ':' || c == '?' then
        let sd := if sp.allowDirectives then
          { sp with allowDirectives := false, documentEverStarted := true } else sp
        match scanNextToken_dispatchBlockIndicators sd c with
        | .ok (some _) =>
          let cl := scanValueClearKey sd
          let premises := shape sp != shape s && sp.flowLevel == 0
            && sp.simpleKey.pos.col == sp.col && sp.simpleKey.possible
            && (c != ':' || sd.explicitKeyLine.isNone || cl.simpleKey.possible)
          let refuted := !atSequenceIndent sp
          if premises then
            inScope := inScope + 1
            if !refuted then inViol := inViol + 1
          else
            outside := outside + 1
            if !refuted then outViol := outViol + 1
        | _ => pure ()
    | _ => break
    match scanNextToken s with
    | .ok (some s') => s := s'
    | _ => break
  return (inScope, inViol, outside, outViol)

def testCursorFaceScope (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 46c: item 378 (PR #144 review) — seqTop_refuted_at_indicator's premises read at every accepted indicator pause: in-scope pauses (pop, no flow, saved key at the cursor, possible, surviving/dead) vs observations outside the lemma; the refutation holds on both"
  -- Predicted before the run: `inViol = outViol = 0` everywhere (HELD 12/12); `inScope > 0` at a
  -- dedent `:` — HELD on `k:⏎  - a⏎: b` (1), REFUTED on `a:⏎- b⏎: c` (a sequence at its
  -- parent's indent pushed no level, so nothing pops: item 377's reading); counts pinned from the run.
  let rows : List (String × String × (Nat × Nat × Nat × Nat)) :=
    [ ("k:⏎  - a⏎: b (`:` at the mapping's indent after a sequence: dead register)", "k:\n  - a\n: b", (1, 0, 1, 0)),
      ("a:⏎- b⏎: c (sequence at its parent's indent: dead register)", "a:\n- b\n: c", (0, 0, 2, 0)),
      ("? a⏎: b (the explicit pair: the live register clears the key)", "? a\n: b", (0, 0, 2, 0)),
      ("? a⏎: b⏎c: d", "? a\n: b\nc: d", (0, 0, 3, 0)),
      ("- ? a⏎  : b (compact explicit pair in a sequence)", "- ? a\n  : b", (0, 0, 2, 0)),
      ("k:⏎  ? a⏎  : b (explicit pair nested in a mapping: the `?` accepted, the `:` cleared)", "k:\n  ? a\n  : b", (0, 0, 3, 0)),
      ("? a⏎? b⏎: c (two explicit keys)", "? a\n? b\n: c", (0, 0, 3, 0)),
      ("? a⏎:⏎? b⏎: c (two explicit pairs, the first value empty)", "? a\n:\n? b\n: c", (0, 0, 4, 0)),
      ("? a⏎⏎: b (blank line between)", "? a\n\n: b", (0, 0, 2, 0)),
      ("? a⏎  k: v⏎: b (block mapping as the explicit key; REFUTED (0, 0, 0, 1, 0): the scanner refuses the inner `k:` itself — misindentedExplicitValue at 1:3 — so no pause is accepted)", "? a\n  k: v\n: b", (0, 0, 1, 0)),
      ("- a⏎- b⏎: c (refused at the sequence top: no accepted pause)", "- a\n- b\n: c", (0, 0, 0, 0)),
      ("a: 1⏎b: 2 (no indicator line)", "a: 1\nb: 2", (0, 0, 2, 0)) ]
  for (label, input, expected) in rows do
    let got := cursorFaceScopeWalk input
    check state s!"cursor-face premises over the accepted pauses of {label}: (inScope, inViol, outside, outViol) = {got}; expected {expected}" (got == expected)

/-- Every field of `ScannerState` rendered VERBATIM — the input string itself, every token with
    its positions (`Positioned` derives `Repr`), every stack — so two states with equal
    fingerprints agree on every field (`ScannerState` derives no `BEq`). -/
def stateFingerprint (s : ScannerState) : String :=
  s!"{repr s.input}|{s.inputEnd}|{s.offset}|{s.line}|{s.col}|{repr s.indents}|{repr s.pendingKeys}|" ++
  s!"{s.flowLevel}|{repr s.tokens}|{repr s.simpleKey}|{repr s.simpleKeyStack}|" ++
  s!"{s.simpleKeyAllowed}|{s.needIndentCheck}|{s.allowDirectives}|{s.seenYamlDirective}|" ++
  s!"{s.directivesPresent}|{s.documentEverStarted}|{repr s.flowStack}|{repr s.explicitKeyLine}|" ++
  s!"{repr s.implicitValueLine}|{repr s.docStartLine}|{s.explicitKeyCol}|{repr s.explicitKeyStack}|" ++
  s!"{repr s.comments}|{repr s.definedAnchors}"

/-- Item 378 (PR #144 review): `scanValueClearKey_id_of_ek_none` claims FULL state equality
    on a dead register.  Over every preprocessing pause of an input (and its directive-reset
    twin), `(checked, bad, live)`: dead-register pauses compared whole by
    `stateFingerprint` (`ScannerState` derives no `BEq`), the ones that differ, and the live-register pauses the
    lemma does not speak to (reported apart, not as refutations). -/
def deadRegisterWalk (input : String) (fuel : Nat := 64) : Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut checked := 0
  let mut bad := 0
  let mut live := 0
  for _ in [:fuel] do
    match scanNextToken_preprocess s with
    | .ok (some (sp, _)) =>
      let sd := if sp.allowDirectives then
        { sp with allowDirectives := false, documentEverStarted := true } else sp
      for st in [sp, sd] do
        if st.explicitKeyLine.isNone then
          checked := checked + 1
          if stateFingerprint (scanValueClearKey st) != stateFingerprint st then bad := bad + 1
        else live := live + 1
    | _ => pure ()
    match scanNextToken s with
    | .ok (some s') => s := s'
    | _ => break
  return (checked, bad, live)

/-- Hand-built dead-register states off the scanner's path: the fields the clear could touch
    set to non-default values, so a clear that rewrote any of them would show. -/
def deadRegisterStates : List (String × ScannerState) :=
  let base := ScannerState.mk' "k: v"
  [ ("default", base),
    ("key disallowed, in flow, col 7",
      { base with simpleKeyAllowed := false, flowLevel := 1, flowStack := #[true], col := 7 }),
    ("possible key at (3, 2) on a pushed level 2",
      { base with
          simpleKey := { base.simpleKey with possible := true, pos := { line := 3, col := 2, offset := 9 } }
          indents := base.indents.push { column := 2, isSequence := false }
          line := 3, col := 2, offset := 9 }),
    ("explicitKeyCol 4 with the line dead", { base with explicitKeyCol := 4, col := 4 }) ]

def testDeadRegisterIdentity (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 46b: item 378 (PR #144 review) — a dead register leaves the key clear alone, the WHOLE state compared (scanValueClearKey_id_of_ek_none); live-register pauses reported apart"
  -- Predicted before the run: `bad = 0` on every row (HELD 6/6); `checked`/`live` pinned from
  -- the run (each pause counted twice: itself and its reset twin; live `?` pauses apart).
  let rows : List (String × String × (Nat × Nat × Nat)) :=
    [ ("k:⏎  - a⏎: b", "k:\n  - a\n: b", (12, 0, 0)),
      ("a:⏎- b⏎: c", "a:\n- b\n: c", (12, 0, 0)),
      ("? a⏎: b", "? a\n: b", (4, 0, 4)),
      ("- ? a⏎  : b", "- ? a\n  : b", (6, 0, 4)),
      ("? a⏎:⏎? b⏎: c", "? a\n:\n? b\n: c", (6, 0, 8)),
      ("a: 1⏎b: 2", "a: 1\nb: 2", (12, 0, 0)) ]
  for (label, input, expected) in rows do
    let got := deadRegisterWalk input
    check state s!"dead-register identity over the pauses of {label}: (checked, bad, live) = {got}; expected {expected}" (got == expected)
  for (label, st) in deadRegisterStates do
    check state s!"dead-register identity on a built state ({label})"
      (stateFingerprint (scanValueClearKey st) == stateFingerprint st)

def testCursorFace (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 46: item 378 — at an accepted `:`/`?` landing the cursor is never on a sequence top (seqTop_refuted_at_indicator), the clear keeps a surviving key (scanValueClearKey_keep), the reset twin keeps the face (atSequenceIndent_disp), a pop puts the cursor under currentIndent; the `:`'s survival disjunct classified (dead register paid, live register the declined residue)"
  -- (viol, ekNone, survive, cleared, quest) over the accepted indicator pauses.  `viol` must be 0
  -- on every row; `survive` is predicted 0 everywhere: at a LINE-START pause the saved key sits at
  -- the cursor (offset equal, line ≠ the `?`'s), so a live register always clears it — the `:`
  -- the builders pay is the one with a dead register.
  let rows : List (String × String × (Nat × Nat × Nat × Nat × Nat)) :=
    [ ("k:⏎  - a⏎: b (`:` at the mapping's indent after a sequence: dead register)", "k:\n  - a\n: b", (0, 1, 0, 0, 0)),
      ("a:⏎- b⏎: c (sequence at its parent's indent: dead register)", "a:\n- b\n: c", (0, 1, 0, 0, 0)),
      ("? a⏎: b (the explicit pair: the live register clears the key)", "? a\n: b", (0, 0, 0, 1, 0)),
      ("? a⏎: b⏎c: d", "? a\n: b\nc: d", (0, 0, 0, 1, 0)),
      ("- ? a⏎  : b (compact explicit pair in a sequence)", "- ? a\n  : b", (0, 0, 0, 1, 0)),
      ("k:⏎  ? a⏎  : b (explicit pair nested in a mapping: the `?` accepted, the `:` cleared)", "k:\n  ? a\n  : b", (0, 0, 0, 1, 1)),
      ("? a⏎? b⏎: c (two explicit keys)", "? a\n? b\n: c", (0, 0, 0, 1, 1)),
      ("? a⏎:⏎? b⏎: c (two explicit pairs, the first value empty)", "? a\n:\n? b\n: c", (0, 0, 0, 2, 1)),
      ("? a⏎⏎: b (blank line between)", "? a\n\n: b", (0, 0, 0, 1, 0)),
      ("? a⏎  k: v⏎: b (block mapping as the explicit key; REFUTED (0, 0, 0, 1, 0): the scanner refuses the inner `k:` itself — misindentedExplicitValue at 1:3 — so no pause is accepted)", "? a\n  k: v\n: b", (0, 0, 0, 0, 0)),
      ("- a⏎- b⏎: c (refused at the sequence top: no accepted pause)", "- a\n- b\n: c", (0, 0, 0, 0, 0)),
      ("a: 1⏎b: 2 (no indicator line)", "a: 1\nb: 2", (0, 0, 0, 0, 0)) ]
  for (label, src, expected) in rows do
    let got := cursorFaceWalk src
    checkM state s!"cursor face at an accepted indicator {label}" (got == expected && got.1 == 0)
      s!"(viol, ekNone, survive, cleared, quest) = {repr got}; expected {repr expected}"

/-- One line-start `:` pause read for item 379 (Priority 47), on the directives-adjusted state
    `sd`: is the register LIVE (`explicitKeyLine = some _`) and does the clear KILL the saved key
    (`(scanValueClearKey sd).simpleKey.possible = false`) — the one `h_surv` disjunct item 378
    left declined at the two builders — and, if so, does the dispatcher accept the `:` while the
    cursor stands on a sequence top (`atSequenceIndent sd`)?  `(liveCleared, seqTop, accepted)`;
    `none` when the pause is not a live-cleared `:`. -/
def liveRegisterRow (sd : ScannerState) (c : Char) : Option (Bool × Bool) :=
  if c == ':' && sd.explicitKeyLine.isSome && !(scanValueClearKey sd).simpleKey.possible then
    some (atSequenceIndent sd, match scanNextToken_dispatchBlockIndicators sd ':' with
      | .ok (some _) => true
      | _ => false)
  else none

/-- Over the line-start pauses of `input` (as `openerSeqTopWalk`, the walk ending at the scanner's
    first refusal): `(liveSeqTopOk, liveSeqTopRefused, liveClearOk, liveClearRefused, visited)` — the
    live-cleared `:` pauses on a sequence top accepted / refused by the dispatcher, the ones not on a
    sequence top accepted / refused, and the pauses visited.  Item 379's question (item 378's NEXT)
    is whether `liveSeqTopOk` can be non-zero: it is the domain of the one `h_surv` decline left at
    `accum_block_on_pendingBlock`/`accum_block_on_pendingBlockContent`. -/
def liveRegisterSeqTopWalk (input : String) (fuel : Nat := 64) : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut seqOk := 0
  let mut seqRefused := 0
  let mut clearOk := 0
  let mut clearRefused := 0
  let mut visited := 0
  for _ in [:fuel] do
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      if sp.line != s.line then
        visited := visited + 1
        let sd := if sp.allowDirectives then
          { sp with allowDirectives := false, documentEverStarted := true } else sp
        match liveRegisterRow sd c with
        | some (true, true) => seqOk := seqOk + 1
        | some (true, false) => seqRefused := seqRefused + 1
        | some (false, true) => clearOk := clearOk + 1
        | some (false, false) => clearRefused := clearRefused + 1
        | none => pure ()
    | _ => break
    match scanNextToken s with
    | .ok (some s') => s := s'
    | _ => break
  return (seqOk, seqRefused, clearOk, clearRefused, visited)

def testLiveRegisterSeqTop (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 47: item 379 — can a live register's `:` whose key the clear kills stand on a sequence top and be accepted?  (the one h_surv decline item 378 left at the two builders; liveSeqTopOk must be 0 on every row)"
  -- Predicted before the run: `liveSeqTopOk = 0` everywhere — a live-cleared `:` must stand at
  -- `currentIndent` (`misindentedExplicitValue` otherwise), and the level at `currentIndent` is the
  -- `?`'s mapping, never a sequence (a `?` on a sequence top is refused, Priority 45; a compact
  -- `- ? a` puts the mapping at the `?`'s column, above the sequence's).  The other four counts are
  -- pinned from the first run (9506/9518: the twelve rows' placeholders; `liveSeqTopOk = 0` on all).
  -- The parser's verdict is PINNED per row (PR #145 review): nine accepted, three refused — the
  -- refusals the labels claim are enforced, not printed.
  let rows : List (String × String × (Nat × Nat × Nat × Nat × Nat) × Bool) :=
    [ ("- ? a⏎: b (compact explicit key, `:` at the SEQUENCE's column: refused, no live-cleared pause visited)", "- ? a\n: b", (0, 0, 0, 0, 1), false),
      ("- ? a⏎  : b (compact explicit key, `:` at the `?`'s column: live-cleared, accepted, on the MAPPING top)", "- ? a\n  : b", (0, 0, 1, 0, 1), true),
      ("? - a⏎: b (sequence as the explicit key)", "? - a\n: b", (0, 0, 1, 0, 1), true),
      ("- ? - a⏎  : b (sequence as a compact explicit key)", "- ? - a\n  : b", (0, 0, 1, 0, 1), true),
      ("? a⏎- b⏎: c (a `-` at the `?`'s column after the key: the scanner refuses the `- b` line, the walk ends before the `:`)", "? a\n- b\n: c", (0, 0, 0, 0, 1), false),
      ("- - ? a⏎    : b (doubly compact)", "- - ? a\n    : b", (0, 0, 1, 0, 1), true),
      ("-⏎  ? a⏎  : b (explicit pair inside an entry)", "-\n  ? a\n  : b", (0, 0, 1, 0, 2), true),
      ("- ? a⏎  : b⏎- c (a sibling entry after the pair)", "- ? a\n  : b\n- c", (0, 0, 1, 0, 2), true),
      ("? a⏎:⏎- b⏎: c (empty explicit value, then a sequence, then a `:`)", "? a\n:\n- b\n: c", (0, 0, 1, 0, 3), true),
      ("? a⏎: b (the explicit pair at the root)", "? a\n: b", (0, 0, 1, 0, 1), true),
      ("k:⏎  ? a⏎  : b (explicit pair nested in a mapping)", "k:\n  ? a\n  : b", (0, 0, 1, 0, 2), true),
      ("- a⏎? b⏎: c (`?` on the sequence top: refused before any `:`)", "- a\n? b\n: c", (0, 0, 0, 0, 1), false) ]
  for (label, src, expected, accepted) in rows do
    let got := liveRegisterSeqTopWalk src
    let ok := match L4YAML.TokenParser.parseYaml src with | .ok _ => true | .error _ => false
    checkM state s!"live register's `:` on a sequence top {label}" (got == expected && got.1 == 0 && ok == accepted)
      s!"(liveSeqTopOk, liveSeqTopRefused, liveClearOk, liveClearRefused, visited) = {repr got} accepted={ok}; expected {repr expected} accepted={accepted}"

/-- One line-start pause read for item 380 (Priority 48): did the break POP the indent stack
    (`sp.indents ≠ s.indents`), and does the landing stand at the pre-state's own level
    (`sp.col = s.currentIndent`)?  The root sibling `b: 2` after `a: 1` is the NO-POP, OWN-LEVEL
    landing — item 378's named residue at the two builders, which the own-level re-read of
    item 380 pays from the park's compact tail, not from a frame below the level. -/
def rootSiblingLevelWalk (input : String) (fuel : Nat := 64) : Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut noPopOwn := 0
  let mut noPopOther := 0
  let mut popped := 0
  let mut visited := 0
  for _ in [:fuel] do
    match scanNextToken_preprocess s with
    | .ok (some (sp, _)) =>
      if sp.line != s.line then
        visited := visited + 1
        let shape : ScannerState → Array (Int × Bool) := fun st => st.indents.map fun e => (e.column, e.isSequence)
        if shape sp == shape s then
          if (sp.col : Int) == s.currentIndent then noPopOwn := noPopOwn + 1 else noPopOther := noPopOther + 1
        else popped := popped + 1
    | _ => break
    match scanNextToken s with
    | .ok (some s') => s := s'
    | _ => break
  return (noPopOwn, noPopOther, popped, visited)

def testRootSiblingLevel (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 48: item 380 — the accepted root sibling LANDS with no pop at the park's OWN level (the entry's compact tail), never a level below it; this walk reads the scanner's landing only — WHICH ARM the two splitting builders take is a term-level fact, pinned by Tests/Guards/Proofs/OpenerFallbackReach.lean's builder-split leaves (PR #146 review)"
  -- Predicted before the run: every root sibling row has noPopOwn ≥ 1 and the parser reads ONE
  -- document (Priority 44's reading); counts pinned from the run.
  let rows : List (String × String × (Nat × Nat × Nat × Nat) × Bool) :=
    [ ("a: 1⏎b: 2", "a: 1\nb: 2", (1, 0, 0, 1), true),
      ("a: 1⏎b: 2⏎c: 3", "a: 1\nb: 2\nc: 3", (2, 0, 0, 2), true),
      ("? a⏎b: 2", "? a\nb: 2", (1, 0, 0, 1), true),
      ("a: [1, 2]⏎b: 2", "a: [1, 2]\nb: 2", (1, 0, 0, 1), true),
      ("a:⏎  x: 1⏎b: 2 (the sibling after a dedent: a POP, not the own level)", "a:\n  x: 1\nb: 2", (0, 1, 1, 2), true),
      ("k:⏎  a: 1⏎  b: 2 (nested sibling at the nested level)", "k:\n  a: 1\n  b: 2", (1, 1, 0, 2), true),
      ("- a: 1⏎  b: 2 (sibling inside a sequence entry)", "- a: 1\n  b: 2", (1, 0, 0, 1), true),
      ("a: 1⏎⏎b: 2 (blank line between)", "a: 1\n\nb: 2", (1, 0, 0, 1), true) ]
  for (label, src, expected, accepted) in rows do
    let got := rootSiblingLevelWalk src
    let ok := match L4YAML.TokenParser.parseYaml src with | .ok _ => true | .error _ => false
    checkM state s!"root sibling at the own level {label}" (got == expected && ok == accepted)
      s!"(noPopOwn, noPopOther, popped, visited) = {repr got} accepted={ok}; expected {repr expected} accepted={accepted}"

/-- The root's KEYS: (documents, the first document's root keys as text in order, the root's first
    item rendered).  Arity is not identity (PR #141 review): a result that duplicated the first pair or
    dropped `b: 2` would still have two entries, so the test reads WHICH keys survive — `["a", "b"]`, in
    that order — and the first value's own contents (a mapping as its keys, a sequence as its scalar
    items, so `a: [1, 2]` reads `["1", "2"]` and a dropped flow element is a refutation too).  A
    non-scalar key (`[1]: a`) renders as `"<non-scalar>"`. -/
def rootKeys (input : String) : Option (Nat × List String × List String) :=
  let text : L4YAML.YamlValue → String := fun k => (k.asString?).getD "<non-scalar>"
  let keys : L4YAML.YamlValue → List String
    | .mapping _ pairs _ _ => (pairs.map (fun (k, _) => text k)).toList
    | _ => []
  let render : L4YAML.YamlValue → List String
    | .mapping _ pairs _ _ => (pairs.map (fun (k, _) => text k)).toList
    | .sequence _ items _ _ => (items.map text).toList
    | _ => []
  let firstItem : L4YAML.YamlValue → List String
    | .mapping _ pairs _ _ => match pairs[0]? with | some (_, v) => render v | none => []
    | .sequence _ items _ _ => match items[0]? with | some v => render v | none => []
    | _ => []
  match L4YAML.TokenParser.parseYaml input with
  | .ok docs => match docs[0]? with
    | some d => some (docs.size, keys d.value, firstItem d.value)
    | none => some (docs.size, [], [])
  | .error _ => none

/-- **Priority 44 (item 376): the openers' root sibling is a RESUME of the root mapping, not a
    second bare document.**  Item 376 priced the park route field's decline face and found no sink
    beneath `pendingMapValue.h_close` — the optional faces decline INTO it.  The way left for the
    seven fallback arms is the one the parser already takes: at a frameless root sibling
    (`a: 1⏎b: 2`) the document count stays at ONE (the key continues the root mapping), it is `---`
    alone that makes a second document, and a sibling key after a sequence top or a plain scalar is
    REFUSED.  Read off `L4YAML.TokenParser.parseYaml` as the root's KEYS in order — a document count or an entry count could not tell a continued mapping from one that dropped or duplicated a key; predictions written before the run. -/
def testRootSiblingResumes (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 44: item 376 — a root sibling continues the root mapping (one document, root keys [a, b] in order); only `---` opens a second; sequence-top/scalar siblings refused"
  let rows : List (String × String × Option (Nat × List String × List String)) :=
    [ ("a: 1⏎b: 2 (`:` opener, root sibling)", "a: 1\nb: 2", some (1, ["a", "b"], [])),
      ("? a⏎b: 2 (`?` opener, sibling with the value empty)", "? a\nb: 2", some (1, ["a", "b"], [])),
      ("a: [1, 2]⏎b: 2 (flow value then a block sibling: the flow elements survive too)", "a: [1, 2]\nb: 2", some (1, ["a", "b"], ["1", "2"])),
      ("[1]: a⏎b: 2 (flow key at the root then a sibling)", "[1]: a\nb: 2", some (1, ["<non-scalar>", "b"], [])),
      ("- a: 1⏎  b: 2 (compact mapping in a sequence entry: one item holding both keys)", "- a: 1\n  b: 2", some (1, [], ["a", "b"])),
      ("a: 1⏎⏎b: 2 (blank line between siblings)", "a: 1\n\nb: 2", some (1, ["a", "b"], [])),
      ("a: 1⏎# c⏎b: 2 (comment line between siblings)", "a: 1\n# c\nb: 2", some (1, ["a", "b"], [])),
      ("k:⏎  a: 1⏎  b: 2⏎c: 3 (closeThenBlock dedent to a root sibling)", "k:\n  a: 1\n  b: 2\nc: 3", some (1, ["k", "c"], ["a", "b"])),
      ("a: 1⏎---⏎b: 2 (the marker alone makes a second document)", "a: 1\n---\nb: 2", some (2, ["a"], [])),
      ("- a⏎b: 2 (sequence top then a key: refused)", "- a\nb: 2", none),
      ("a⏎b: 2 (plain scalar then a key: refused)", "a\nb: 2", none) ]
  for (label, src, expected) in rows do
    let got := rootKeys src
    checkM state s!"root sibling {label}" (got == expected)
      s!"(documents, root keys, first item rendered) = {repr got}; expected {repr expected}"

/-- **Priority 49 (item 381): the `-` park's NO-POP `:`/`?` arm receives a key indicator after a
    CLOSED entry node.**  Item 380's mandate asked the two splitting builders to pay the no-pop
    landing by continuing the awaited node's compact mapping; the build refuted it at the type —
    at both builders the node is already closed (`h_ssl` is the comments run `SSLComments sp_gram
    sp_mid`, the node itself is closed over inside `h_closeF_old`).  So the sibling of
    `- a: 1⏎  b: 2` never reaches that arm: it lands on the mapping's own park.  What does reach
    it is a `:`/`?` at an unchanged stack after a closed node: refused after a closed scalar or flow
    node, while `? b` after a plain scalar is the scalar's own continuation and `: b` after an
    EMPTY entry node is the node itself (`[189]`'s empty-key entry) — the first run refuted the
    two predictions that said otherwise.  SCOPE (§7): these rows read the parser's VERDICT and
    the root's SHAPE; WHICH park's arm receives the indicator is not observable from the parser
    and is not what the rows claim — that is read off the proof terms (the refuting build's type,
    `h_ssl : SSLComments`, and `OpenerFallbackReach`'s builder-split leaves).  Read
    off `L4YAML.TokenParser.parseYaml` as `rootKeys` (verdict + root shape), predictions in the
    rows. -/
def testNoPopAfterClosedNode (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 49: item 381 — parser VERDICT + root SHAPE only: a `:`/`?` after a CLOSED sequence-entry node at an unchanged stack is refused (scalar/flow node), is the scalar's continuation (`? b`), or IS the node (`: b` after an empty entry); the compact-mapping sibling and the explicit entry's value are accepted — WHICH park's arm receives them is a term-level fact (§7), read off the proof terms, not here"
  let rows : List (String × String × Option (Nat × List String × List String)) :=
    [ ("- a⏎  : b (`:` after a closed plain scalar, deeper, no pop)", "- a\n  : b", none),
      ("- a⏎  ? b (`? b` CONTINUES the plain scalar — the node is not closed; accepted as one scalar)", "- a\n  ? b", some (1, [], [])),
      ("-⏎  : b (after an EMPTY entry node the `:` IS the node: `[189]`'s empty-key entry, accepted)", "-\n  : b", some (1, [], [""])),
      ("- a⏎  : (bare `:` after a closed scalar)", "- a\n  :", none),
      ("- \"a\"⏎  : b (`:` after a closed quoted scalar)", "- \"a\"\n  : b", none),
      ("- [a]⏎  : b (`:` after a closed flow node)", "- [a]\n  : b", none),
      ("- a: 1⏎  b: 2 (the compact mapping's sibling: the MAPPING park's, accepted)", "- a: 1\n  b: 2", some (1, [], ["a", "b"])),
      ("- ? a⏎  : b (the explicit entry's value: the `?` park's, accepted)", "- ? a\n  : b", some (1, [], ["a"])) ]
  for (label, src, expected) in rows do
    let got := rootKeys src
    checkM state s!"no-pop after a closed node {label}" (got == expected)
      s!"(documents, root keys, first item rendered) = {repr got}; expected {repr expected}"

/-- **Priority 50 (item 382): the MAPPING park's NO-POP arm receives the DEEPER landing — the
    awaited VALUE node — while the root sibling takes the RESUME arm.**  `flip_own_tail.py`, now `scripts/flips/item382_own_tail.json` read
    that every birth of `pendingMapValue` already supplies `h_frames` with the park's own level as
    the head frame (`ResumeFrames.level k ksF …` over the empty value, item 147/197), so at
    `accum_block_on_closeThenBlock` the `hmem` test is TRUE for a sibling at the park's level
    (`a:⏎b: 2`): the resume arm, not the no-pop one.  What reaches the no-pop arm (`hmem` false,
    stack unchanged) is a `:`/`?` landing DEEPER than the park — the value node of `a:` — which the
    openers' tail-shaped `h_res_land` cannot resume: the design question item 382 names.  Scope
    (§7): the rows read `L4YAML.TokenParser.parseYaml`'s VERDICT and the root's SHAPE as `rootKeys`
    (verdict + root keys + the first value's rendering); which park's arm receives a landing is a
    proof-term fact — the flip's types and `OpenerFallbackReach`'s builder-split leaves — not
    something a parser row observes.  Predictions in the rows. -/
def testDeeperLandingOnMapPark (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 50: item 382 — parser VERDICT + root SHAPE only: a root sibling after an EMPTY mapping value (`a:⏎b: 2`, through comments, explicit entry) is ONE mapping of two keys; a DEEPER `:`/`?`/`-`/scalar landing is `a`'s VALUE node; a root sibling after a nested value lands after a pop — WHICH park's arm receives each (resume / no-pop / popped) is a term-level fact (§7), read off the proof terms, not here"
  let rows : List (String × String × Option (Nat × List String × List String)) :=
    [ ("a:⏎b: 2 (root sibling after an EMPTY value: the park's own level is the head frame — RESUME arm; one mapping)", "a:\nb: 2", some (1, ["a", "b"], [])),
      ("? a⏎:⏎b: 2 (explicit entry, empty value, root sibling — resume)", "? a\n:\nb: 2", some (1, ["a", "b"], [])),
      ("a:⏎# c⏎b: 2 (a comment line inside the comments run before the sibling)", "a:\n# c\nb: 2", some (1, ["a", "b"], [])),
      ("a:⏎b: (two empty values)", "a:\nb:", some (1, ["a", "b"], [])),
      ("a:⏎  b: 2 (DEEPER `:` landing: the value NODE of `a`, nested mapping — the no-pop arm's domain)", "a:\n  b: 2", some (1, ["a"], ["b"])),
      ("a:⏎  ? b⏎  : c (deeper `?` landing: the value node, explicit entry)", "a:\n  ? b\n  : c", some (1, ["a"], ["b"])),
      ("a:⏎  - b (deeper `-`: the value node is a sequence)", "a:\n  - b", some (1, ["a"], ["b"])),
      ("a:⏎  b (deeper scalar: the value is the scalar `b`)", "a:\n  b", some (1, ["a"], [])),
      ("a:⏎ b: 2⏎ c: 3 (one-space deeper landing + its own sibling: nested mapping of two)", "a:\n b: 2\n c: 3", some (1, ["a"], ["b", "c"])),
      ("a:⏎  b: 2⏎c: 3 (deeper landing, then the ROOT sibling after a pop: the popped arm)", "a:\n  b: 2\nc: 3", some (1, ["a", "c"], ["b"])) ]
  for (label, input, expected) in rows do
    let got := rootKeys input
    checkM state s!"deeper landing vs root sibling on a mapping park {label}" (got == expected)
      s!"(documents, root keys, first value rendered) = {repr got}; expected {repr expected}"

/-- Priority 51 (item 383): the deeper landing's two parks, read as parser VERDICT + root SHAPE only
    (§7 — WHICH arm of `h_vslot` receives the landing is a term-level fact, read off the proof terms).
    Rows: the SLOT arm (empty value, deeper `:`/`?`/`-` is `a`'s value node — accepted) against the
    RESIDUE arm (value already inline — `a: x⏎  b: 2` — the deeper landing is REFUSED). -/
def testDeeperLandingResidueArm (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 51: item 383 — parser VERDICT + root SHAPE only: a deeper `:`/`?`/`-` after an EMPTY mapping value is `a`'s value node (the slot arm, accepted); after an INLINE value (scalar, flow, quoted, with a trailing comment) the same landing is refused (the residue arm — `h_vslot`'s second disjunct, which carries no route); the sibling after an inline value is accepted (the resume arm) — which arm receives each is a term-level fact (§7), read off the proof terms, not here"
  let rows : List (String × String × Option (Nat × List String × List String)) :=
    [ ("a:⏎  b: 2 (SLOT arm: empty value, deeper `:` — `a`'s value node, a nested mapping)", "a:\n  b: 2", some (1, ["a"], ["b"])),
      ("a:⏎  ? b⏎  : c (slot arm: deeper explicit entry)", "a:\n  ? b\n  : c", some (1, ["a"], ["b"])),
      ("a:⏎  - x (slot arm: deeper sequence value — `firstItem` renders the sequence's items)", "a:\n  - x", some (1, ["a"], ["x"])),
      ("a: x⏎  b: 2 (RESIDUE arm: plain scalar already inline, deeper `:` — refused)", "a: x\n  b: 2", none),
      ("a: 'x'⏎  b: 2 (residue arm: quoted scalar inline — refused)", "a: 'x'\n  b: 2", none),
      ("a: [x]⏎  b: 2 (residue arm: flow value inline — refused)", "a: [x]\n  b: 2", none),
      ("a: x # c⏎  b: 2 (residue arm: inline scalar with a trailing comment — refused)", "a: x # c\n  b: 2", none),
      ("a: x⏎  ? b⏎  : c (residue arm: deeper `?` after an inline scalar — refused)", "a: x\n  ? b\n  : c", none),
      ("a: x⏎  - y (NOT a landing: the plain scalar continues onto the next line — ACCEPTED, one key, a scalar value; the reader does not see scalar contents, the `\"x - y\"` reading is the probe's)", "a: x\n  - y", some (1, ["a"], [])),
      ("a: x⏎b: 2 (the SIBLING after an inline value: the resume arm, one mapping of two keys)", "a: x\nb: 2", some (1, ["a", "b"], [])) ]
  for (label, input, expected) in rows do
    let got := rootKeys input
    checkM state s!"deeper landing: slot vs residue arm {label}" (got == expected)
      s!"(documents, root keys, first value rendered) = {repr got}; expected {repr expected}"

/-- **Priority 51 (S5 slice 1, EVENTSOF-CONCEPT §9): the parser's serialization verdict vs
    `checkFrom {} (tokenEvents tokens)`.**  S5(→) claims that every `parseStream` run the parser
    accepts is a run `checkFrom` accepts on the tokens it consumed.  Rows pair the parser's verdict
    on `scanFiltered input` with the checker's on the same tokens (`none` = the scanner refused
    before either could speak); a `(true, false)` row anywhere refutes the lemma and fails the
    build.  The scanner-shape premises the lemma carries (`TagUsesShaped`: tag-use handles are
    `""`/`!`/`!!`/`!w+!`; `DirectivesClosed`: a directive run ends at `---`) and the
    `streamEnd`-last shape that makes the consumed prefix the whole array are read as Booleans
    on every scanned row, so the lemma's conclusion is exactly `checkFrom {} (tokenEvents ts)`
    there.  Four hand-built token arrays pin the token-level GAP the premises exist for
    (`parseStream` ok, `checkFrom` false): a `%TAG !h` handle without its closing `!`, the loop's
    no-progress exit at a bare `key`, tokens after `streamEnd`, and a directive run with no `---`.
    Closing or widening that gap (a parser, scanner or `tokenEvents` change) fails this grid. -/
def s5Verdict (input : String) : Option (Bool × Bool) :=
  match Scanner.scanFiltered input with
  | .error _ => none
  | .ok ts =>
    let parserOk := match parseStream ts with | .ok _ => true | .error _ => false
    some (parserOk, L4YAML.Proofs.Serialization.SerializationWellFormed.checkFrom {}
      (L4YAML.Proofs.Serialization.TokenEvents.tokenEvents ts))

def s5TokVerdict (ts : Array (Positioned YamlToken)) : Bool × Bool :=
  let parserOk := match parseStream ts with | .ok _ => true | .error _ => false
  (parserOk, L4YAML.Proofs.Serialization.SerializationWellFormed.checkFrom {}
    (L4YAML.Proofs.Serialization.TokenEvents.tokenEvents ts))

def s5TagUsesShaped (ts : Array (Positioned YamlToken)) : Bool :=
  ts.all fun p => match p.val with
    | .tag h _ => h == "" || h == "!" || h == "!!" || L4YAML.Proofs.Serialization.TokenEvents.isNamedHandle h
    | _ => true

def s5IsDirective : Option YamlToken → Bool
  | some (.versionDirective ..) | some (.tagDirective ..) => true
  | _ => false

def s5DirectivesClosed (ts : Array (Positioned YamlToken)) : Bool :=
  (List.range ts.size).all fun i =>
    !s5IsDirective (ts[i]?.map (·.val)) ||
      s5IsDirective (ts[i+1]?.map (·.val)) || (ts[i+1]?.map (·.val)) == some .documentStart

def s5StreamEndLast (ts : Array (Positioned YamlToken)) : Bool :=
  ts.size > 0 && (ts[ts.size - 1]?.map (·.val)) == some .streamEnd

def s5Tok (t : YamlToken) : Positioned YamlToken := { val := t, pos := { offset := 0, line := 0, col := 0 } }

def testParseOkCheckFrom (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 51: S5 slice 1 — parser verdict vs checkFrom {} (tokenEvents ts) on scanFiltered input (a (true,false) row refutes parse_ok_checkFrom); scanner-shape premises read as Booleans; the token-level gap A–D pinned as parseStream ok ∧ checkFrom false"
  let accept : Option (Bool × Bool) := some (true, true)
  let reject : Option (Bool × Bool) := some (false, false)
  let rows : List (String × String × Option (Bool × Bool)) :=
    [ ("empty stream", "", accept),
      ("one bare document", "a", accept),
      ("one explicit document", "--- a\n", accept),
      ("two documents with `...` and `---` resets", "--- a\n...\n--- b\n", accept),
      ("two documents, `---` only", "a\n---\nb", accept),
      ("&x a (anchor, no alias)", "&x a", accept),
      ("[&x a, *x] (alias after its anchor)", "[&x a, *x]", accept),
      ("&x [*x] (self-reference: declaration-set reading)", "&x [*x]", accept),
      ("&x [*x, *x]", "&x [*x, *x]", accept),
      ("{&x a: *x}", "{&x a: *x}", accept),
      ("%TAG !t! declared then used", "%TAG !t! tag:x,2000:\n--- !t!a b", accept),
      ("%TAG !t! re-declared in document 2", "%TAG !t! tag:x,2000:\n--- !t!a b\n...\n%TAG !t! tag:y,2000:\n--- !t!c d", accept),
      ("!!str a (secondary handle)", "!!str a", accept),
      ("! a (non-specific tag)", "! a", accept),
      ("!<tag:x> a (verbatim tag)", "!<tag:x> a", accept),
      ("!a b (primary handle with suffix)", "!a b", accept),
      ("%TAG !h … (unclosed handle: scanner refuses since spec [89] is enforced)", "%TAG !h tag:x,2000:\n--- !h x", none),
      ("%TAG !! redefined", "%TAG !! tag:x,2000:\n--- !!a b", accept),
      ("%TAG ! redefined", "%TAG ! tag:x,2000:\n--- !a b", accept),
      ("duplicate anchor across `...` reset", "--- &x a\n...\n--- &x b", accept),
      ("duplicate anchor across `---` reset", "--- &x a\n--- &x b", accept),
      ("%YAML 1.2 then document", "%YAML 1.2\n--- a", accept),
      ("%TAG declared, never used", "%TAG !t! tag:x,2000:\n--- a", accept),
      ("? a (explicit key)", "? a", accept),
      ("!t!a without a declaration", "--- !t!a b", reject),
      ("!t! used in document 2 after `...` (declaration does not survive the reset)", "%TAG !t! tag:x,2000:\n--- !t!a b\n...\n--- !t!c d", reject),
      ("!t! used in document 2 after `---`", "%TAG !t! tag:x,2000:\n--- a\n--- !t!b", reject),
      ("!t! used after `...` with no `---`", "%TAG !t! tag:x,2000:\n--- !t!a\n...\n!t!b", reject),
      ("!a-b!c d (undeclared named handle)", "!a-b!c d", reject),
      (": !t!a", ": !t!a", reject),
      ("- !t!x", "- !t!x", reject),
      ("a: !t!x", "a: !t!x", reject),
      ("*x undeclared (scanner refuses)", "*x", none),
      ("*x in document 2 after `...`", "--- &x a\n...\n--- *x", none),
      ("*x in document 2 after `---`", "&x a\n--- *x", none),
      ("[*x, &x a] (alias before its anchor)", "[*x, &x a]", none),
      ("&a &b x (two anchors)", "&a &b x", none),
      ("%TAG !a_b! (malformed handle)", "%TAG !a_b! tag:x,2000:\n--- a", none),
      ("stray `]`", "]", none),
      ("stray `}`", "}", none),
      ("stray `, a`", ", a", none) ]
  for (label, src, expected) in rows do
    let got := s5Verdict src
    checkM state s!"S5 verdict {label}" (got == expected)
      s!"(parser ok, checkFrom) = {repr got}; expected {repr expected}"
    checkM state s!"S5(→) never parser-ok/checker-false {label}" (got != some (true, false))
      s!"parser accepted what checkFrom rejects: {repr got}"
    match Scanner.scanFiltered src with
    | .error _ => pure ()
    | .ok ts =>
      checkM state s!"S5 scanner shape (TagUsesShaped ∧ DirectivesClosed ∧ streamEnd last) {label}"
        (s5TagUsesShaped ts && s5DirectivesClosed ts && s5StreamEndLast ts)
        s!"tokens = {repr (ts.map (·.val)).toList}"
  let gap : List (String × Array (Positioned YamlToken)) :=
    [ ("A: `%TAG !h` handle without its closing `!` (parser registers it, tokenEvents declares only named handles)",
        #[s5Tok .streamStart, s5Tok (.tagDirective "!h" "p"), s5Tok .documentStart, s5Tok (.tag "!h" "x"), s5Tok .streamEnd]),
      ("B1: no-progress exit at a bare `key` before a tag use", #[s5Tok .streamStart, s5Tok .key, s5Tok (.tag "!t!" "x"), s5Tok .streamEnd]),
      ("B2: no-progress exit at a bare `key` before an undeclared alias",
        #[s5Tok .streamStart, s5Tok (.scalar "a" .plain), s5Tok .key, s5Tok (.alias "x"), s5Tok .streamEnd]),
      ("C: tokens after `streamEnd`", #[s5Tok .streamStart, s5Tok .streamEnd, s5Tok (.tag "!t!" "x")]),
      ("D: directive run with no `---`", #[s5Tok .streamStart, s5Tok (.tagDirective "!t!" "p"), s5Tok (.tag "!t!" "x"), s5Tok .streamEnd]) ]
  for (label, ts) in gap do
    let got := s5TokVerdict ts
    -- the B rows (no-progress exit) are refused since (γ2α): the parser no longer accepts them
    let exp := if label.startsWith "B" then (false, false) else (true, false)
    checkM state s!"S5 token-level gap pinned {label}" (got == exp)
      s!"(parser ok, checkFrom) = {repr got}; expected {repr exp} — the premises of parseStream_ok_checkFrom exist for this gap"
    checkM state s!"S5 token-level gap is outside the premises {label}"
      (!(s5TagUsesShaped ts && s5DirectivesClosed ts && s5StreamEndLast ts) || label.startsWith "B")
      s!"the gap input satisfies the scanner-shape premises; only the no-progress rows (B) may"

/-- Priority 52 (item 385): the deeper landing PAID at the two parks' no-pop arms, read as parser
    VERDICT + root SHAPE only (§7 — which arm pays is a term-level fact, read off `deeperLandingResume`
    and `deeperLandingResumeSeq`).  Rows: the mapping park's deeper `:`/`?` after an EMPTY value is
    `a`'s value node (paid from `h_valF`); the `-` park's deeper `:` on the next line is the awaited
    entry's node (paid from `pendingBlock.h_closeF`); the dedent rows the helpers still decline are
    the SIBLING (resume arm, item 382) and the popped landing (item 378), not the deeper one.
    §7 SCOPE: these rows read the PARSER (verdict + shape) and cannot see which route a proof
    term takes — a helper whose body were `Or.inr trivial` would leave them green.  The
    helpers' informative side is pinned where it is observable, on the proof terms:
    `Tests/Guards/Proofs/ConclusionRouteCensus.lean` (`deeperLandingResume#0 :: DECLINE | DECLINE | PAY`,
    `deeperLandingResumeSeq#0 :: DECLINE | PAY` — a declining body reads `DECLINE` alone and fails the pin),
    `ConclusionCensus` (`inl=1`), `RelaySupplyCensus` (SPLIT BRANCH `VIA deeperLandingResume = 2`,
    `VIA deeperLandingResumeSeq = 1`) and `OpenerFallbackReach` (the `pendingBlock` leaf). -/
def testDeeperLandingPaid (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 52: item 385 — parser VERDICT + root SHAPE only: the deeper `:`/`?` landing after an empty mapping value or a bare `-` is the park's own node"
  let rows : List (String × String × Option (Nat × List String × List String)) :=
    [ ("a:⏎  b: 2 (mapping park, deeper `:` — `a`'s value is a nested mapping)", "a:\n  b: 2", some (1, ["a"], ["b"])),
      ("a:⏎  b: 2⏎  c: 3 (mapping park, deeper mapping of two keys — the compact tail)", "a:\n  b: 2\n  c: 3", some (1, ["a"], ["b", "c"])),
      ("a:⏎  ? b⏎  : c (mapping park, deeper explicit entry)", "a:\n  ? b\n  : c", some (1, ["a"], ["b"])),
      ("a:⏎    b: 2 (mapping park, deeper by more than one level — any k ≥ nv + 1)", "a:\n    b: 2", some (1, ["a"], ["b"])),
      ("-⏎  a: 1 (`-` park, deeper `:` on the next line — the entry's node is a mapping)", "-\n  a: 1", some (1, [], ["a"])),
      ("-⏎  a: 1⏎  b: 2 (`-` park, deeper mapping of two keys)", "-\n  a: 1\n  b: 2", some (1, [], ["a", "b"])),
      ("-⏎  ? a⏎  : 1 (`-` park, deeper explicit entry)", "-\n  ? a\n  : 1", some (1, [], ["a"])),
      ("a:⏎b: 2 (the SIBLING — resume arm, item 382: declined by the helpers, paid upstream)", "a:\nb: 2", some (1, ["a", "b"], [])),
      ("a:⏎  b:⏎c: 3 (popped landing after a deeper empty value — item 378's arm)", "a:\n  b:\nc: 3", some (1, ["a", "c"], ["b"])),
      ("a:⏎ b: 2 (deeper by ONE column: k = nv + 1 exactly, the helpers' boundary)", "a:\n b: 2", some (1, ["a"], ["b"])) ]
  for (label, input, expected) in rows do
    let got := rootKeys input
    checkM state s!"deeper landing paid: {label}" (got == expected)
      s!"(documents, root keys, first value rendered) = {repr got}; expected {repr expected}"

/-- **Priority 55 (S5 slice 2 Rule-2 guard, EVENTSOF-CONCEPT §9): the two token-event
extractors on the guard inputs of `Tests/Guards/Proofs/TokenEventExtractors.lean`.**  Every
row runs the parser (`parseStream`), `checkTokenGrammar`, the OLD state verdict
(the retired checkTokenState over tokenEventsOf, recorded as literals), the NEW one
(`checkFrom {} (tokenEvents ts)`, over `TokenEvents.tokenEvents`) and whether the two traces
are equal.  Scanner rows: parser and both verdicts agree on all 32, the traces agree on 31 —
the scanner-reachable witness `%TAG !h …⏎--- !h x` is the one trace seam (verdicts still
agree).  Token rows pin the gaps A/D/D'/E (old true, new false except D'), the no-progress
and post-`streamEnd` shapes B1/B2/C, and R1–R6: on R1/R3 `checkTokenGrammar` ∧ new verdict
hold while the parser REFUSES — the refutation of ruling (c) under the un-narrowed
`TG.DocStart` that the guard file records. -/
def testTokenEventExtractorsSeam (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 55: S5 slice 2 guard — tokenEventsOf vs tokenEvents: parser / TG / old / new verdicts and trace equality on the %TAG seam, A/B/C/D/D'/E and R1–R6"
  let ev₂ (ts : Array (Positioned YamlToken)) := L4YAML.Proofs.Serialization.TokenEvents.tokenEvents ts
  let newV (ts : Array (Positioned YamlToken)) : Bool :=
    L4YAML.Proofs.Serialization.SerializationWellFormed.checkFrom {} (ev₂ ts)
  let pOk (ts : Array (Positioned YamlToken)) : Bool := match TokenParser.parseStream ts with | .ok _ => true | .error _ => false
  let tg (ts : Array (Positioned YamlToken)) : Bool := L4YAML.Proofs.TokenGrammar.checkTokenGrammar ts
  -- scanner rows: (input, parser ok, old = new verdict, traces equal)
  let srows : List (String × Bool × Bool × Bool) :=
    [ ("", true, true, true), ("a", true, true, true), ("--- a\n", true, true, true),
      ("--- a\n...\n--- b\n", true, true, true), ("a\n---\nb", true, true, true),
      ("%TAG !t! tag:x,2000:\n--- !t!a b", true, true, true),
      ("%TAG !t! tag:x,2000:\n%TAG !u! tag:y,2000:\n--- !u!a b", true, true, true),
      ("%TAG !t! tag:x,2000:\n%TAG !t! tag:y,2000:\n--- !t!a b", true, true, true),
      ("%YAML 1.2\n%TAG !t! tag:x,2000:\n--- !t!a b", true, true, true),
      ("%TAG !t! tag:x,2000:\n%YAML 1.2\n--- !t!a b", true, true, true),
      ("%TAG !t! tag:x,2000:\n--- !t!a b\n...\n%TAG !t! tag:y,2000:\n--- !t!c d", true, true, true),
      ("%TAG !t! tag:x,2000:\n--- !t!a b\n...\n--- !t!c d", false, false, true),
      ("%TAG !t! tag:x,2000:\n--- a\n--- !t!b", false, false, true),
      ("%TAG !t! tag:x,2000:\n--- !t!a\n...\n!t!b", false, false, true),
      ("%TAG !! tag:x,2000:\n--- !!a b", true, true, true), ("%TAG ! tag:x,2000:\n--- !a b", true, true, true),
      ("%TAG !t! tag:x,2000:\n--- a", true, true, true), ("--- !t!a b", false, false, true), ("!!str a", true, true, true),
      ("! a", true, true, true), ("!<tag:x> a", true, true, true), ("!a b", true, true, true), ("&x a", true, true, true),
      ("[&x a, *x]", true, true, true), ("&x [*x]", true, true, true), ("{&x a: *x}", true, true, true),
      ("--- &x a\n...\n--- &x b", true, true, true), ("--- &x a\n--- &x b", true, true, true), ("? a", true, true, true),
      ("a: !t!x", false, false, true), ("%TAG !t! tag:x,2000:\n---\n...\n--- !t!a", false, false, true),
      ("%TAG !t! tag:x,2000:\n--- !t!a\n---\n!t!b", false, false, true) ]
  -- the `%TAG !h` witness no longer scans: spec [89] `c-tag-handle` is enforced (`invalidTagHandle`)
  checkM state "P55 %TAG !h witness: scanner refuses with invalidTagHandle"
    (match Scanner.scanFiltered "%TAG !h tag:x,2000:\n--- !h x" with
     | .error (.invalidTagHandle "!h" _ _) => true | _ => false) "unclosed handle still scans"
  for (src, ep, ev, eq) in srows do
    match Scanner.scanFiltered src with
    | .error e => checkM state s!"P55 scanner row scans {repr src}" false s!"scan error {repr e}"
    | .ok ts =>
      -- `eq = false` marks the one row where the retired extractor's reading differed (the `%TAG !h`
      -- witness): there the surviving trace is asserted literally, against the retired reading's literal
      checkM state s!"P55 {repr src}: parser={ep} new={ev} (retired extractor agreed={eq})"
        (pOk ts == ep && newV ts == ev) s!"got parser={pOk ts} new={newV ts}"
      if !eq then
        checkM state s!"P55 {repr src}: tokenEvents = [beginDocument, useTag !] ≠ retired [beginDocument, declareTag !h, useTag !]"
          (ev₂ ts == [.beginDocument, .useTag "!"] &&
           ev₂ ts != [.beginDocument, .declareTag "!h", .useTag "!"])
          s!"got {repr (ev₂ ts)}"
  let mk (t : YamlToken) : Positioned YamlToken := { val := t, pos := { offset := 0, line := 0, col := 0 } }
  -- token rows: (label, tokens, parser ok, TG (narrowed, spec [209]), retired-extractor verdict as a literal, new verdict)
  let trows : List (String × Array (Positioned YamlToken) × Bool × Bool × Bool × Bool) :=
    [ ("A %TAG !h + use", #[mk .streamStart, mk (.tagDirective "!h" "p"), mk .documentStart, mk (.tag "!h" "x"), mk .streamEnd], true, true, true, false),
      ("B1 key at doc start", #[mk .streamStart, mk .key, mk (.tag "!t!" "x"), mk .streamEnd], false, false, false, false),
      ("B2 scalar key alias", #[mk .streamStart, mk (.scalar "a" .plain), mk .key, mk (.alias "x"), mk .streamEnd], false, false, false, false),
      ("C after streamEnd", #[mk .streamStart, mk .streamEnd, mk (.tag "!t!" "x")], true, false, false, false),
      ("D directives, no ---, use", #[mk .streamStart, mk (.tagDirective "!t!" "p"), mk (.tag "!t!" "x"), mk .streamEnd], true, false, true, false),
      ("D' directive then streamEnd", #[mk .streamStart, mk (.tagDirective "!t!" "p"), mk .streamEnd], true, false, true, true),
      ("E %TAG !a_b!", #[mk .streamStart, mk (.tagDirective "!a_b!" "p"), mk .documentStart, mk (.tag "!a_b!" "x"), mk .streamEnd], true, true, true, false),
      ("R1 --- &x a %TAG *x", #[mk .streamStart, mk .documentStart, mk (.anchor "x"), mk (.scalar "a" .plain), mk (.tagDirective "!t!" "p"), mk (.alias "x"), mk .streamEnd], false, false, false, true),
      ("R2 --- &x a ... %TAG *x", #[mk .streamStart, mk .documentStart, mk (.anchor "x"), mk (.scalar "a" .plain), mk .documentEnd, mk (.tagDirective "!t!" "p"), mk (.alias "x"), mk .streamEnd], false, false, false, false),
      ("R3 --- &x a %YAML *x", #[mk .streamStart, mk .documentStart, mk (.anchor "x"), mk (.scalar "a" .plain), mk (.versionDirective 1 2), mk (.alias "x"), mk .streamEnd], false, false, false, true),
      ("R4 &x a %TAG --- *x", #[mk .streamStart, mk (.anchor "x"), mk (.scalar "a" .plain), mk (.tagDirective "!t!" "p"), mk .documentStart, mk (.alias "x"), mk .streamEnd], false, true, false, false),
      ("R5 %TAG !t!x a (no ---)", #[mk .streamStart, mk (.tagDirective "!t!" "p"), mk (.tag "!t!" "x"), mk (.scalar "a" .plain), mk .streamEnd], true, false, true, false),
      ("R6 --- a %TAG !t!x b (no ---)", #[mk .streamStart, mk .documentStart, mk (.scalar "a" .plain), mk (.tagDirective "!t!" "p"), mk (.tag "!t!" "x"), mk (.scalar "b" .plain), mk .streamEnd], true, false, true, false) ]
  for (label, ts, ep, etg, eold, enew) in trows do
    checkM state s!"P55 {label}: parser={ep} TG={etg} new={enew} (retired verdict was {eold})"
      (pOk ts == ep && tg ts == etg && newV ts == enew)
      s!"got parser={pOk ts} TG={tg ts} new={newV ts}"
  -- the parser's registration follows the OLD extractor: wherever old and new differ, old = parser
  for (label, ts, _ep, _etg, eold, enew) in trows do
    if eold != enew then
      checkM state s!"P55 {label}: parser follows the retired reading" (pOk ts == eold) s!"parser={pOk ts} recorded={eold}"
  -- R1/R3: `TG ∧ new verdict` with the parser refusing — ruling (c) refuted as stated
  checkM state "P55 no row has TokenGrammar ∧ checkFrom (tokenEvents ts) with parseStream refusing (R1/R3 closed by [209])"
    ((trows.filter (fun r => tg r.2.1 && newV r.2.1 && !pOk r.2.1)).length == 0) "parseStream_accepts refuted"

/-- **Priority 54 (S5 slice 1 review, EVENTSOF-CONCEPT §9): `ParseNodeCF` instantiated
directly — `parseNode` from a hand-built parse state at EVERY position of short block and
flow streams, fuel 0/1/2/3 and "enough".**  Rule 2 for `parseNode_cf_all : ∀ n, ParseNodeCF n`
(7.7 `parse_iff_grammar` via S5), whose scope is any parser state and any fuel, not the
whole-input verdicts Priority 51 compares.  For each `(ts, p, fuel)` the state is
`{ tokens := ts, pos := p }` (and, for the alias rows, the same state with `x` declared), the
hypothesis is `parseNode ps fuel = .ok (_, ps')` together with `TagUsesShaped ts`, and the
claim is `CF ps ps'` run executably: same tokens, `ps.pos ≤ ps'.pos`, tag table unchanged,
in-range stays in-range, and `runToks (seg ts ps.pos ps'.pos)` from the state the entry sits
below (its declared anchors and named handles) succeeds at a state the exit sits below.
Rows whose hypothesis fails (`parseNode` errors — fuel out, position on a closer, an
undeclared alias — or an unshaped tag use) are counted as **failed-hypothesis**, apart from
the **theorem-holds** rows; the grid requires both buckets non-empty and the hypothesis to
hold at fuel 1 and 2 somewhere, so the claim is exercised, not vacuous. -/
def testParseNodeCF (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 54: S5 slice 1 — ParseNodeCF at every position of short streams, fuel 0/1/2/3/enough (theorem-holds vs failed-hypothesis)"
  let named (hs : Array (String × String)) : List String := (hs.toList.map (·.1)).filter L4YAML.Proofs.Serialization.TokenEvents.isNamedHandle
  let shaped (ts : Array (Positioned YamlToken)) : Bool := ts.all fun t => match t.val with
    | .tag h _ => h == "" || h == "!" || h == "!!" || L4YAML.Proofs.Serialization.TokenEvents.isNamedHandle h
    | _ => true
  let cfTwin (ps ps' : ParseState) : Bool :=
    ps'.tokens.size == ps.tokens.size &&
    (List.zip ps'.tokens.toList ps.tokens.toList).all (fun ab => ab.1.val == ab.2.val) &&
    decide (ps.pos ≤ ps'.pos) && ps'.tagHandles == ps.tagHandles &&
    (!decide (ps.pos ≤ ps.tokens.size) || decide (ps'.pos ≤ ps.tokens.size)) &&
    (let s₀ : L4YAML.Proofs.Serialization.ParseCheckFrom.CS :=
       ({ anchors := ps.declaredAnchors.toList, tagHandles := named ps.tagHandles }, [])
     match L4YAML.Proofs.Serialization.ParseCheckFrom.runToks
         (L4YAML.Proofs.Serialization.ParseCheckFrom.seg ps.tokens ps.pos ps'.pos) s₀ with
     | some s' => ps'.declaredAnchors.all (fun a => s'.1.anchors.contains a) &&
                  (named ps'.tagHandles).all (fun h => s'.1.tagHandles.contains h)
     | none => false)
  let srcs : List String :=
    [ "a", "&x a", "[&x a, *x]", "{a: &y b, c: *y}", "- a\n- &x b\n- *x", 
      "!!str a", "! a", "!<tag:x> a", "%TAG !t! tag:x,2000:\n--- !t!a b",
      "&x [*x, {k: *x}]", "- [a, b]\n- {c: d}", "? a\n: b",  
      "- &x\n  - a\n- *x", "a:\n  b: &x c\n  d: *x", "--- !!map {a: !!str b}", "[&x a, &x b, *x]" ]
  let mk (t : YamlToken) : Positioned YamlToken := { val := t, pos := { offset := 0, line := 0, col := 0 } }
  let hand : List (String × Array (Positioned YamlToken)) :=
    [ ("A unshaped %TAG !h + use", #[mk .streamStart, mk (.tagDirective "!h" "p"), mk .documentStart, mk (.tag "!h" "x"), mk .streamEnd]),
      ("E unshaped !a_b!", #[mk .streamStart, mk (.tagDirective "!a_b!" "p"), mk .documentStart, mk (.tag "!a_b!" "x"), mk .streamEnd]),
      ("alias then anchor", #[mk .streamStart, mk .flowSequenceStart, mk (.alias "x"), mk .flowEntry, mk (.anchor "x"), mk (.scalar "a" .plain), mk .flowSequenceEnd, mk .streamEnd]),
      -- undeclared aliases are refused by the scanner, so they only exist as token rows
      ("map value alias undeclared", #[mk .streamStart, mk .blockMappingStart, mk .key, mk (.scalar "a" .plain), mk .value, mk (.scalar "b" .plain), mk .key, mk (.scalar "c" .plain), mk .value, mk (.alias "x"), mk .blockEnd, mk .streamEnd]),
      ("alias across ---", #[mk .streamStart, mk .documentStart, mk (.anchor "x"), mk (.scalar "a" .plain), mk .documentEnd, mk .documentStart, mk (.alias "x"), mk .streamEnd]),
      ("nested flow alias before anchor", #[mk .streamStart, mk .flowSequenceStart, mk (.scalar "a" .plain), mk .flowEntry, mk .flowSequenceStart, mk (.scalar "b" .plain), mk .flowEntry, mk (.alias "x"), mk .flowSequenceEnd, mk .flowEntry, mk (.anchor "x"), mk (.scalar "c" .plain), mk .flowSequenceEnd, mk .streamEnd]) ]
  let holds ← IO.mkRef (0 : Nat)
  let failed ← IO.mkRef (0 : Nat)
  let fuel12 ← IO.mkRef (0 : Nat)
  let streams : List (String × Array (Positioned YamlToken)) ←
    (srcs.filterMapM fun src => do
      match Scanner.scanFiltered src with
      | .ok ts => pure (some (s!"{repr src}", ts))
      | .error e => checkM state s!"P54 {repr src} scans" false s!"scan error {repr e}"; pure none)
  for (label, ts) in streams ++ hand do
    for p in List.range (ts.size + 1) do
      for fuel in [0, 1, 2, 3, 60] do
        for (seed, ps) in [("", ({ tokens := ts, pos := p } : ParseState)),
                           (" +&x", ({ tokens := ts, pos := p } : ParseState).declareAnchor "x")] do
          let row := s!"P54 {label} pos={p} fuel={fuel}{seed}"
          if !shaped ts then
            failed.modify (· + 1)
            checkM state s!"{row}: failed-hypothesis (TagUsesShaped)" true ""
          else
            match TokenParser.parseNode ps fuel with
            | .error _ =>
              failed.modify (· + 1)
              checkM state s!"{row}: failed-hypothesis (parseNode errors)" true ""
            | .ok (_, ps') =>
              holds.modify (· + 1)
              if fuel == 1 || fuel == 2 then fuel12.modify (· + 1)
              checkM state s!"{row}: theorem-holds — CF ps ps'" (cfTwin ps ps')
                s!"CF refuted: pos {ps.pos} → {ps'.pos}, declared {repr ps'.declaredAnchors}, tags {repr ps'.tagHandles}"
  let (h, f, f12) := (← holds.get, ← failed.get, ← fuel12.get)
  checkM state s!"P54 buckets: theorem-holds={h} failed-hypothesis={f} (hypothesis holds at fuel 1/2 on {f12} rows)"
    (h ≥ 100 && f ≥ 100 && f12 ≥ 20) "the grid is vacuous on one bucket"

/-- **Priority 53 (S5 slice 2, EVENTSOF-CONCEPT §9): `TokenStateOk` before and after its
restatement over `TokenEvents.tokenEvents`.**  Rule 2 before the restatement: every row
records the parser verdict, `checkTokenGrammar`, the OLD state verdict (the per-token
`tokEvents` reading, as a literal — the public definition disappears) and the NEW one
(`checkFrom {} (tokenEvents ts)`).  Scanner rows must agree before/after; the token-level
rows A/D/E/R5/R6 flip true → false (the `%TAG` seam: unclosed handle, `---`-less directive
run — vacuous for `parseStream_accepts`), D' stays true, and R1/R3 flip false → TRUE with
the parser REFUSING — the refutation of the restatement under the un-narrowed `TG.DocStart`,
closed by narrowing `DocStart` to spec [209] (`---` after a non-empty directive run), which
this grid pins as `TG = false` on R1/R3. -/
def testTokenStateOkRestatement (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 53: S5 slice 2 — TokenStateOk over tokenEvents: parser / TG / old / new verdicts on the %TAG seam, the ---less directive run (R1–R6) and A/D/D'/E"
  let newV (ts : Array (Positioned YamlToken)) : Bool :=
    L4YAML.Proofs.Serialization.SerializationWellFormed.checkFrom {} (L4YAML.Proofs.Serialization.TokenEvents.tokenEvents ts)
  let pOk (ts : Array (Positioned YamlToken)) : Bool := match TokenParser.parseStream ts with | .ok _ => true | .error _ => false
  let tg (ts : Array (Positioned YamlToken)) : Bool := L4YAML.Proofs.TokenGrammar.checkTokenGrammar ts
  -- scanner rows: (input, parser ok, old = new verdict)
  let srows : List (String × Bool × Bool) :=
    [ ("", true, true), ("a", true, true), ("--- a\n", true, true), ("--- a\n...\n--- b\n", true, true), ("a\n---\nb", true, true),
      ("%TAG !t! tag:x,2000:\n--- !t!a b", true, true),
      ("%TAG !t! tag:x,2000:\n%TAG !u! tag:y,2000:\n--- !u!a b", true, true),
      ("%TAG !t! tag:x,2000:\n%TAG !t! tag:y,2000:\n--- !t!a b", true, true),
      ("%YAML 1.2\n%TAG !t! tag:x,2000:\n--- !t!a b", true, true),
      ("%TAG !t! tag:x,2000:\n%YAML 1.2\n--- !t!a b", true, true),
      ("%TAG !t! tag:x,2000:\n--- !t!a b\n...\n%TAG !t! tag:y,2000:\n--- !t!c d", true, true),
      ("%TAG !t! tag:x,2000:\n--- !t!a b\n...\n--- !t!c d", false, false),
      ("%TAG !t! tag:x,2000:\n--- a\n--- !t!b", false, false),
      ("%TAG !t! tag:x,2000:\n--- !t!a\n...\n!t!b", false, false),
      ("%TAG !! tag:x,2000:\n--- !!a b", true, true), ("%TAG ! tag:x,2000:\n--- !a b", true, true),
      ("%TAG !t! tag:x,2000:\n--- a", true, true), ("--- !t!a b", false, false), ("!!str a", true, true),
      ("! a", true, true), ("!<tag:x> a", true, true), ("!a b", true, true), ("&x a", true, true),
      ("[&x a, *x]", true, true), ("&x [*x]", true, true), ("{&x a: *x}", true, true),
      ("--- &x a\n...\n--- &x b", true, true), ("--- &x a\n--- &x b", true, true), ("? a", true, true),
      ("a: !t!x", false, false), ("%TAG !t! tag:x,2000:\n---\n...\n--- !t!a", false, false),
      ("%TAG !t! tag:x,2000:\n--- !t!a\n---\n!t!b", false, false) ]
  let live ← IO.mkRef (0 : Nat)   -- rows on which BOTH premises of `parseStream_accepts` hold
  let implication (label : String) (ts : Array (Positioned YamlToken)) : IO Unit := do
    let (g, n, p) := (tg ts, newV ts, pOk ts)
    if g && n then live.modify (· + 1)
    checkM state s!"P53 {label}: TokenGrammar ∧ checkFrom (tokenEvents ts) → parseStream ok (live: TG={g} new={n})"
      (!(g && n) || p) s!"parseStream_accepts refuted: TG={g} new={n} parser={p}"
  -- the `%TAG !h` witness no longer scans: spec [89] `c-tag-handle` is enforced (`invalidTagHandle`)
  checkM state "P53 %TAG !h witness: scanner refuses with invalidTagHandle"
    (match Scanner.scanFiltered "%TAG !h tag:x,2000:\n--- !h x" with
     | .error (.invalidTagHandle "!h" _ _) => true | _ => false) "unclosed handle still scans"
  for (src, ep, ev) in srows do
    match Scanner.scanFiltered src with
    | .error e => checkM state s!"P53 scanner row scans {repr src}" false s!"scan error {repr e}"
    | .ok ts =>
      checkM state s!"P53 {repr src}: parser={ep} old=new={ev}" (pOk ts == ep && newV ts == ev)
        s!"got parser={pOk ts} new={newV ts}"
      -- scanner output IS in the grammar wherever the parser accepts it (StreamCompleteness's converse)
      checkM state s!"P53 {repr src}: parser ok → TokenGrammar" (!(pOk ts) || tg ts) s!"parser ok but TG={tg ts}"
      implication s!"{repr src}" ts
  let mk (t : YamlToken) : Positioned YamlToken := { val := t, pos := { offset := 0, line := 0, col := 0 } }
  -- token rows: (label, tokens, parser ok, TG after narrowing, old verdict, new verdict)
  let trows : List (String × Array (Positioned YamlToken) × Bool × Bool × Bool × Bool) :=
    [ ("A %TAG !h + use", #[mk .streamStart, mk (.tagDirective "!h" "p"), mk .documentStart, mk (.tag "!h" "x"), mk .streamEnd], true, true, true, false),
      ("B1 key at doc start", #[mk .streamStart, mk .key, mk (.tag "!t!" "x"), mk .streamEnd], false, false, false, false),
      ("B2 scalar key alias", #[mk .streamStart, mk (.scalar "a" .plain), mk .key, mk (.alias "x"), mk .streamEnd], false, false, false, false),
      ("C after streamEnd", #[mk .streamStart, mk .streamEnd, mk (.tag "!t!" "x")], true, false, false, false),
      ("D directives, no ---, use", #[mk .streamStart, mk (.tagDirective "!t!" "p"), mk (.tag "!t!" "x"), mk .streamEnd], true, false, true, false),
      ("D' directive then streamEnd", #[mk .streamStart, mk (.tagDirective "!t!" "p"), mk .streamEnd], true, false, true, true),
      ("E %TAG !a_b!", #[mk .streamStart, mk (.tagDirective "!a_b!" "p"), mk .documentStart, mk (.tag "!a_b!" "x"), mk .streamEnd], true, true, true, false),
      ("R1 --- &x a %TAG *x", #[mk .streamStart, mk .documentStart, mk (.anchor "x"), mk (.scalar "a" .plain), mk (.tagDirective "!t!" "p"), mk (.alias "x"), mk .streamEnd], false, false, false, true),
      ("R2 --- &x a ... %TAG *x", #[mk .streamStart, mk .documentStart, mk (.anchor "x"), mk (.scalar "a" .plain), mk .documentEnd, mk (.tagDirective "!t!" "p"), mk (.alias "x"), mk .streamEnd], false, false, false, false),
      ("R3 --- &x a %YAML *x", #[mk .streamStart, mk .documentStart, mk (.anchor "x"), mk (.scalar "a" .plain), mk (.versionDirective 1 2), mk (.alias "x"), mk .streamEnd], false, false, false, true),
      ("R4 &x a %TAG --- *x", #[mk .streamStart, mk (.anchor "x"), mk (.scalar "a" .plain), mk (.tagDirective "!t!" "p"), mk .documentStart, mk (.alias "x"), mk .streamEnd], false, true, false, false),
      ("R5 %TAG !t!x a (no ---)", #[mk .streamStart, mk (.tagDirective "!t!" "p"), mk (.tag "!t!" "x"), mk (.scalar "a" .plain), mk .streamEnd], true, false, true, false),
      ("R6 --- a %TAG !t!x b (no ---)", #[mk .streamStart, mk .documentStart, mk (.scalar "a" .plain), mk (.tagDirective "!t!" "p"), mk (.tag "!t!" "x"), mk (.scalar "b" .plain), mk .streamEnd], true, false, true, false),
      -- both premises TRUE (the live cases of `parseStream_accepts`): a `---`-closed `%TAG` run, two
      -- documents re-declaring an anchor across `...`/`---`, an alias inside its own node
      ("L1 %TAG !t! --- !t!x a", #[mk .streamStart, mk (.tagDirective "!t!" "p"), mk .documentStart, mk (.tag "!t!" "x"), mk (.scalar "a" .plain), mk .streamEnd], true, true, true, true),
      ("L2 --- &x a ... --- &x *x", #[mk .streamStart, mk .documentStart, mk (.anchor "x"), mk (.scalar "a" .plain), mk .documentEnd, mk .documentStart, mk (.anchor "x"), mk (.scalar "b" .plain), mk .streamEnd], true, true, true, true),
      ("L3 %YAML %TAG --- &x [*x]", #[mk .streamStart, mk (.versionDirective 1 2), mk (.tagDirective "!t!" "p"), mk .documentStart, mk (.anchor "x"), mk .flowSequenceStart, mk (.alias "x"), mk .flowSequenceEnd, mk .streamEnd], true, true, true, true),
      ("L4 --- &x a --- *x (alias across ---)", #[mk .streamStart, mk .documentStart, mk (.anchor "x"), mk (.scalar "a" .plain), mk .documentStart, mk (.alias "x"), mk .streamEnd], false, true, false, false) ]
  for (label, ts, ep, etg, _old, enew) in trows do
    checkM state s!"P53 {label}: parser={ep} TG(narrowed)={etg} new={enew}" (pOk ts == ep && tg ts == etg && newV ts == enew)
      s!"got parser={pOk ts} TG={tg ts} new={newV ts}"
    implication label ts
  -- the implication must have been exercised with both premises true, not vacuously
  let n ← live.get
  checkM state s!"P53 live rows (TG ∧ new both true): {n} ≥ 25" (n ≥ 25) s!"only {n} live rows"

/-- Priority 56 (item 386): L1 at the helpers — under a NO-POP landing the dedent `k < level` is
    absurd and `k = level` is the SIBLING (mapping park) or the SEQUENCE TOP the dispatcher refuses
    (`-` park), read as parser VERDICT + root SHAPE only (§7: which route the helper takes is pinned
    on the proof terms — `ConclusionRouteCensus` `deeperLandingResume#0 :: DECLINE | DECLINE | PAY | PAY`
    — not here).  Rows: the sibling at the park's own level (`a:⏎a2: 1`, accepted, two root keys);
    the sibling one level in (`a:⏎  b:⏎  c: 2`); a `:`/`?` at the `-`'s own column is refused
    (`-⏎a: 1`, `-⏎: y`, `- x⏎: y` — the k = n leaf the `-` helper still declines, named for item 387);
    a dedent INSIDE the park's level is a POPPED landing the parser refuses (`  a:⏎ b: 1`); controls:
    deeper by one, the sequence sibling, a mid-document sibling after an empty value.  Predictions
    pinned before the first run. -/
def testNoPopDedentL1 (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 56: item 386 — parser VERDICT + root SHAPE only: under a no-pop landing the dedent is gone — k = level is the sibling (mapping park) or the refused sequence top (`-` park)"
  let rows : List (String × String × Option (Nat × List String × List String)) :=
    [ ("a:⏎a2: 1 (mapping park, k = nv: the SIBLING at the park's own level — empty value, then the own tail)", "a:\na2: 1", some (1, ["a", "a2"], [])),
      ("a:⏎  b:⏎  c: 2 (inner mapping park `b:`, k = nv one level in — the sibling under the deeper landing)", "a:\n  b:\n  c: 2", some (1, ["a"], ["b", "c"])),
      ("a:⏎  b: 1⏎  c:⏎  d: 2 (inner park after a filled sibling, k = nv)", "a:\n  b: 1\n  c:\n  d: 2", some (1, ["a"], ["b", "c", "d"])),
      ("a: 1⏎b:⏎c: 2 (mid-document sibling after an empty value, k = nv = 0)", "a: 1\nb:\nc: 2", some (1, ["a", "b", "c"], [])),
      ("  a:⏎ b: 1 (dedent INSIDE the park's level: a POPPED landing — refused as trailing content)", "  a:\n b: 1", none),
      ("-⏎a: 1 (`-` park, k = n: a `:` at the `-`'s own column is a SEQUENCE TOP — refused)", "-\na: 1", none),
      ("-⏎: y (`-` park, k = n: a bare `:` at the `-`'s column — refused)", "-\n: y", none),
      ("- x⏎: y (`-` park with an inline scalar, `:` at the `-`'s column — refused)", "- x\n: y", none),
      ("-⏎- b (`-` park, the SEQUENCE sibling: not a `:`/`?` landing, not these helpers)", "-\n- b", some (1, [], [])),
      ("a:⏎ a2: 1 (deeper by ONE column: k = nv + 1, item 385's boundary, still paid)", "a:\n a2: 1", some (1, ["a"], ["a2"])) ]
  for (label, input, expected) in rows do
    let got := rootKeys input
    checkM state s!"L1 no-pop dedent: {label}" (got == expected)
      s!"(documents, root keys, first value rendered) = {repr got}; expected {repr expected}"

open L4YAML.Proofs.PreprocessIndentStable in
/-- Priority 56, Rule 2 for the new floor lemma (PR #157 review): `IndentFloor.int_le_of_succ`
    — `IndentFloor sc (n + 1) → (n : Int) ≤ sc.currentIndent` — instantiated over scanner states
    with an EMPTY stack, the sentinel alone, a singleton level (column 0, mapping and sequence),
    a nested stack (`-1 / 0 / 2`) and a stack whose top is a deeper sequence, at `n ∈ {0, 1, 2, 3}`
    and both indent-check flags.  Each row checks the implication AND pins its bucket — the
    hypothesis `needIndentCheck = false ∧ n + 1 ≤ minContentIndentOf sc` is predicted to hold
    exactly when the flag is down and `n ≤ top` (`-1` for an empty stack), so a vacuous pass is
    visible: 56 rows, 12 **theorem-holds**, 44 **failed-hypothesis**. -/
def testFloorLevelInstances (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 56: item 386 — IndentFloor.int_le_of_succ instantiated over scanner states (empty / sentinel / singleton / nested / sequence tops; n = 0..3; both flags)"
  let base := ScannerState.mk' "x"
  let sent : IndentEntry := { column := -1, isSequence := false }
  let stacks : List (String × Array IndentEntry) :=
    [ ("empty", #[]),
      ("sentinel", #[sent]),
      ("map@0", #[sent, { column := 0, isSequence := false }]),
      ("seq@0", #[sent, { column := 0, isSequence := true }]),
      ("map@0/map@2", #[sent, { column := 0, isSequence := false }, { column := 2, isSequence := false }]),
      ("map@0/seq@2", #[sent, { column := 0, isSequence := false }, { column := 2, isSequence := true }]),
      ("map@0/map@2/map@3", #[sent, { column := 0, isSequence := false }, { column := 2, isSequence := false }, { column := 3, isSequence := false }]) ]
  let mut holds := 0
  let mut failed := 0
  for (label, st) in stacks do
    for nic in [false, true] do
      let sc : ScannerState := { base with indents := st, needIndentCheck := nic }
      let top : Int := (st.back?.map (·.column)).getD (-1)
      for n in [0, 1, 2, 3] do
        let hyp := !sc.needIndentCheck && decide (n + 1 ≤ minContentIndentOf sc)
        let concl := decide ((n : Int) ≤ sc.currentIndent)
        checkM state s!"IndentFloor.int_le_of_succ {label} nic={nic} n={n}: hyp → (n : Int) ≤ currentIndent"
          (!hyp || concl) s!"hyp={hyp} concl={concl} top={top} currentIndent={sc.currentIndent}"
        -- The bucket, predicted: the flag down and `n ≤ top`.
        checkM state s!"IndentFloor.int_le_of_succ {label} nic={nic} n={n}: bucket = {if hyp then "theorem-holds" else "failed-hypothesis"}"
          (hyp == (!nic && decide ((n : Int) ≤ top))) s!"top={top}"
        if hyp then holds := holds + 1 else failed := failed + 1
  checkM state s!"IndentFloor.int_le_of_succ buckets: theorem-holds={holds} failed-hypothesis={failed}"
    (holds == 12 && failed == 44) ""

/-- **Priority 57 (spec [89] `c-tag-handle`): the scanner refuses every `%TAG` handle that is not
`!`, `!!` or `!word!`.**  Rule 2 for the `[89]` refusal (`isTagHandleShaped`, `invalidTagHandle`,
S5's S3 obligation (a) discharged at the scanner): every handle shape × the scanner's verdict, the
parser's verdict on what scans, and `isTagHandleShaped`/`isNamedHandle` agreement on the named
shapes; a shaped handle must still scan and parse exactly as before. -/
def testTagHandleShape (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 57: spec [89] c-tag-handle — %TAG handle shapes: refused iff not !, !! or !word!"
  let shaped := L4YAML.Scanner.isTagHandleShaped
  let named := L4YAML.Proofs.Serialization.TokenEvents.isNamedHandle
  -- (handle, shaped?, use that must parse when shaped)
  let rows : List (String × Bool × String) :=
    [ ("!", true, "!a b"), ("!!", true, "!!str b"), ("!t!", true, "!t!a b"), ("!a-b!", true, "!a-b!a b"),
      ("!9!", true, "!9!a b"), ("!A!", true, "!A!a b"), ("!h", false, "!h x"), ("!a_b!", false, "!a_b!a b"),
      ("!t!t!", false, "!t!a b"), ("!!x", false, "!!x b"), ("h", false, "a"), ("!-!", true, "!-!a b"),
      ("!", true, "a") ]
  for (h, sh, use) in rows do
    let src := s!"%TAG {h} tag:x,2000:\n--- {use}"
    checkM state s!"P57 isTagHandleShaped {repr h} = {sh}" (shaped h == sh) s!"got {shaped h}"
    if h != "!" && h != "!!" then
      checkM state s!"P57 {repr h}: named-handle readings agree" (named h == sh) s!"isNamedHandle={named h}"
    match Scanner.scanFiltered src with
    | .error (.invalidTagHandle h' _ _) =>
      -- the refused handle is the run of word-chars/`!` the scanner collected (`!a_b!` stops at `_` → `!a`)
      checkM state s!"P57 {repr src}: refused as invalidTagHandle {repr h'}" (!sh && h.startsWith h' && !shaped h')
        s!"shaped={sh}"
    | .error e => checkM state s!"P57 {repr src}: unexpected scan error" false s!"{repr e}"
    | .ok ts =>
      let pOk := match TokenParser.parseStream ts with | .ok _ => true | .error _ => false
      checkM state s!"P57 {repr src}: scans and parses" (sh && pOk) s!"shaped={sh} parser={pOk}"

/-- Priority 58, Rule 2 for item 387 — parser VERDICT + root SHAPE only (§7: the rows cannot see
    which proof route fired; the informative side is pinned on the proof terms by
    `ConclusionRouteCensus` / `RelaySupplyCensus` / `OpenerFallbackReach`).  The `-` park's `k = n`
    landing is TWO inputs: a `:`/`?` at a SEQUENCE top is refused by the dispatcher (the paid half),
    a `:` at a MAPPING top is that mapping's sibling — a `-` at the mapping's own column pushes no
    sequence entry (`pushSequenceIndent` guards `col > currentIndent`), so `a:⏎- b` leaves the mapping
    at `n` on top and `a:⏎-⏎c: 1` is ACCEPTED (the declined half, no route among the park's frames).
    The reader's third component is the root's FIRST ITEM rendered (`a: [b]` reads `["b"]`, an empty
    entry reads `""`); the first run mispredicted it as `[]` on five rows — a reader-side error,
    corrected here; every verdict and key list HELD on the first run. -/
def testSeqTopNoPopFaces (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 58: item 387 — parser VERDICT + root SHAPE only: the `-` park's k = n landing is a refused SEQUENCE top or an accepted MAPPING sibling (the `-` at the mapping's own column pushed nothing)"
  let rows : List (String × String × Option (Nat × List String × List String)) :=
    [ ("a:⏎- b (the `-` at the mapping's own column: no push, the mapping stays on top; a sequence value)", "a:\n- b", some (1, ["a"], ["b"])),
      ("a:⏎-⏎c: 1 (k = n at a MAPPING top: the enclosing mapping's SIBLING — accepted, the declined half)", "a:\n-\nc: 1", some (1, ["a", "c"], [""])),
      ("a:⏎- b⏎c: 1 (same sibling after a filled entry)", "a:\n- b\nc: 1", some (1, ["a", "c"], ["b"])),
      ("a:⏎-⏎- c (k = n, a second `-`: the SEQUENCE sibling, not a `:`/`?` landing)", "a:\n-\n- c", some (1, ["a"], ["", "c"])),
      ("-⏎a: 1 (k = n at a SEQUENCE top, bare park: refused — the paid half)", "-\na: 1", none),
      ("-⏎? x (k = n at a SEQUENCE top, the `?` indicator: refused)", "-\n? x", none),
      ("- a⏎- b (the sequence sibling at a bare park: accepted, not these helpers)", "- a\n- b", some (1, [], [])),
      ("a:⏎  -⏎  c: 1 (the `-` DEEPER than the mapping pushes a sequence at 2; a `:` at 2 is a sequence top: refused)", "a:\n  -\n  c: 1", none),
      ("a:⏎  b:⏎  -⏎  c: 1 (the `-` at the inner mapping's own column pushes nothing; `c:` at 2 is its sibling: accepted)", "a:\n  b:\n  -\n  c: 1", some (1, ["a"], ["b", "c"])),
      ("-⏎ a: 1 (k = n + 1 at a bare `-` park: the deeper landing, item 385's route)", "-\n a: 1", some (1, [], ["a"])) ]
  for (label, input, expected) in rows do
    let got := rootKeys input
    checkM state s!"seq-top vs mapping-sibling at k = n: {label}" (got == expected)
      s!"(documents, root keys, first value rendered) = {repr got}; expected {repr expected}"
  -- The scanner face the site splits on, instantiated: `atSequenceIndent` at a cursor standing
  -- AT the top's column reads the top's KIND — true at a sequence top (the refutation
  -- `seqTop_refuted_at_indicator_le` bites), false at a mapping top (nothing to refute: the
  -- declined half) — and false one column right of the top at either kind (`k = n + 1`,
  -- the helper's domain).  12 rows, 2 predicted sequence-top faces.
  let base := ScannerState.mk' "x"
  let sent : IndentEntry := { column := -1, isSequence := false }
  let stacks : List (String × Array IndentEntry × Nat × Bool) :=
    [ ("map@0", #[sent, { column := 0, isSequence := false }], 0, false),
      ("seq@0", #[sent, { column := 0, isSequence := true }], 0, true),
      ("map@0/map@2", #[sent, { column := 0, isSequence := false }, { column := 2, isSequence := false }], 2, false),
      ("map@0/seq@2", #[sent, { column := 0, isSequence := false }, { column := 2, isSequence := true }], 2, true) ]
  let mut seqFaces := 0
  for (label, st, top, isSeq) in stacks do
    for dk in [0, 1, 2] do
      let sc : ScannerState := { base with indents := st, col := top + dk }
      let face := atSequenceIndent sc
      let hle := decide ((sc.col : Int) ≤ sc.currentIndent)
      checkM state s!"atSequenceIndent {label} col=top+{dk}: face = (sequence top ∧ at its column)"
        (face == (isSeq && dk == 0)) s!"face={face} currentIndent={sc.currentIndent}"
      checkM state s!"seqTop_refuted_at_indicator_le premise {label} col=top+{dk}: col ≤ currentIndent ↔ dk = 0"
        (hle == (dk == 0)) s!"hle={hle}"
      if face then seqFaces := seqFaces + 1
  checkM state s!"atSequenceIndent faces at the top's column: sequence tops = {seqFaces}" (seqFaces == 2) ""

/-- Item 387 (PR #159 review): `seqTop_refuted_at_indicator_le`'s premises read at every ACCEPTED
    `:`/`?` dispatch of `input` (the pause `scanNextToken_preprocess` returns, dispatched on its
    directive-reset twin exactly as the lemma states it).  The lemma's cursor premise is the
    BOUND `col ≤ currentIndent` — not item 378's pop — so a no-pop landing at the top's own
    column is in scope for the first time.  Returns `(inScope, inViol, noPop, outside, outViol,
    cleared)`: pauses where every premise holds (`h_le`, no flow, the saved key at the cursor and
    possible, the `:` surviving `scanValueClearKey` or no explicit key open), those among them at
    which the refutation `atSequenceIndent sp = false` FAILS (a refutation of the lemma), the
    in-scope pauses whose stack is UNCHANGED by preprocessing (the new no-pop domain — the tally
    the site's `k = n` split spends), pauses outside the premises (failed-hypothesis rows: a
    mid-line `:` has `col > currentIndent`), those outside at which the face is nonetheless a
    sequence top (reported, not a refutation), and the outside pauses that failed on the
    live-register conjunct alone (`:` after an open `?`, the key cleared). -/
def seqTopLeDispatchWalk (input : String) (fuel : Nat := 64) :
    Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut inScope := 0
  let mut inViol := 0
  let mut noPop := 0
  let mut outside := 0
  let mut outViol := 0
  let mut cleared := 0
  let shape : ScannerState → Array (Int × Bool) := fun st => st.indents.map fun e => (e.column, e.isSequence)
  for _ in [:fuel] do
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      if c == ':' || c == '?' then
        let sd := if sp.allowDirectives then
          { sp with allowDirectives := false, documentEverStarted := true } else sp
        match scanNextToken_dispatchBlockIndicators sd c with
        | .ok (some _) =>
          let hle := decide ((sp.col : Int) ≤ sp.currentIndent)
          let surv := c != ':' || sd.explicitKeyLine.isNone || (scanValueClearKey sd).simpleKey.possible
          let premises := hle && !sp.inFlow && sp.simpleKey.pos.col == sp.col
            && sp.simpleKey.possible && surv
          let refuted := !atSequenceIndent sp
          if premises then
            inScope := inScope + 1
            if shape sp == shape s then noPop := noPop + 1
            if !refuted then inViol := inViol + 1
          else
            outside := outside + 1
            if !surv then cleared := cleared + 1
            if !refuted then outViol := outViol + 1
        | _ => pure ()
    | _ => break
    match scanNextToken s with
    | .ok (some s') => s := s'
    | _ => break
  return (inScope, inViol, noPop, outside, outViol, cleared)

def testSeqTopLeDispatchWalk (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 58b: item 387 (PR #159 review) — seqTop_refuted_at_indicator_le's premises read at every accepted `:`/`?` dispatch: the bound col ≤ currentIndent puts the NO-POP landing at the top's own column in scope; the refutation holds at every in-scope pause, pop or no pop"
  -- Predicted before the run: `inViol = outViol = 0` on every row; `noPop ≥ 1` on the three
  -- no-push rows (`a:⏎- b⏎: c`, `a:⏎-⏎? x`, `a:⏎  b:⏎  -⏎  : c`) and 0 on the popped row
  -- `k:⏎  - a⏎: b` (item 378's domain, `inScope = 1`); a mid-line `:` is always outside
  -- (`col > currentIndent`); the `:` of an explicit pair is outside on the live-register
  -- conjunct (`cleared`); a `:`/`?` the dispatcher refuses is no pause at all.  Counts pinned
  -- from the run where the prediction was only a sign.  First run 12/13: the `-⏎a: 1` row
  -- predicted one outside pause and read none (the scanner refuses that `:` itself).
  let rows : List (String × String × (Nat × Nat × Nat × Nat × Nat × Nat)) :=
    [ ("a:⏎- b⏎: c (`:` at the mapping's own column after a no-push `-`: NO-POP, in scope, refuted)", "a:\n- b\n: c", (1, 0, 1, 1, 0, 0)),
      ("a:⏎-⏎? x (`?` at the mapping's own column after an empty no-push `-`: NO-POP, in scope)", "a:\n-\n? x", (1, 0, 1, 1, 0, 0)),
      ("a:⏎  b:⏎  -⏎  : c (the same one level down)", "a:\n  b:\n  -\n  : c", (1, 0, 1, 2, 0, 0)),
      ("k:⏎  - a⏎: b (the POPPED landing: item 378's domain, in scope, no no-pop)", "k:\n  - a\n: b", (1, 0, 0, 1, 0, 0)),
      ("k:⏎  - a⏎  : b (`:` ON the sequence top: the dispatcher refuses it — no accepted pause)", "k:\n  - a\n  : b", (0, 0, 0, 1, 0, 0)),
      ("- a⏎: b (root sequence top: refused, no pause)", "- a\n: b", (0, 0, 0, 0, 0, 0)),
      ("-⏎a: 1 (the paid half's input; REFUTED (0, 0, 0, 1, 0, 0): the SCANNER refuses the content-lane key on the sequence top at its `:` (Priority 45's `- a⏎b: 1`), so the `:` is no accepted pause at all — the row has no dispatch to read)", "-\na: 1", (0, 0, 0, 0, 0, 0)),
      ("a:⏎-⏎c: 1 (the declined half's input: both `:` mid-line, outside)", "a:\n-\nc: 1", (0, 0, 0, 2, 0, 0)),
      ("a: 1⏎b: 2 (no indicator line)", "a: 1\nb: 2", (0, 0, 0, 2, 0, 0)),
      ("? a⏎: b (the explicit pair: `?` on the empty stack is outside (-1 < 0), the `:` cleared)", "? a\n: b", (0, 0, 0, 2, 0, 1)),
      ("? a⏎:⏎? b⏎: c (second `?` at the explicit mapping's column: no-pop, in scope; both `:` cleared)", "? a\n:\n? b\n: c", (1, 0, 1, 3, 0, 2)),
      ("- ? a⏎  : b (compact explicit pair in a sequence: the `:` cleared)", "- ? a\n  : b", (0, 0, 0, 2, 0, 1)) ]
  let mut noPopTotal := 0
  for (label, input, expected) in rows do
    let got := seqTopLeDispatchWalk input
    noPopTotal := noPopTotal + got.2.2.1
    check state s!"seqTop_le premises over the accepted dispatches of {label}: (inScope, inViol, noPop, outside, outViol, cleared) = {got}; expected {expected}" (got == expected)
  checkM state s!"seqTop_le: nonvacuous no-pop in-scope dispatches across the rows = {noPopTotal} (predicted 4)" (noPopTotal == 4) s!"got {noPopTotal}"

/-! ## Priority 59b — `valueLandedSeq` INSTANTIATED on constructed derivations (PR #160 review)

Priority 59's 32 lemma rows read only the `seqSpaces` arithmetic the side condition discharges;
a wrong COMPOSITION (the node consuming a different range than its entries) would pass them.
Rule 2 for a `Prop`-valued lemma is a constructed witness (§7: the informative side is
reachability, not a pin): below, `SSLComments` and `SBlockSeqEntries` derivations are BUILT
from characters (as `entryQ`/`streamQ` were for item 343), `valueLandedSeq` is applied, and
its conclusion is pinned at the EXACT endpoint the entries reached — empty entry, two entries,
a nested compact entry, the pushed `nv < k` entry (whose witness also serves `nv = k = 1`), and
an EOF-terminated entry (endpoint at the entry's own column, not reset).  Each `GLit`/`SBBreak`
step is deterministic on its characters, so the endpoint is the one the characters force.
The `nv > k` corner has NO instance: its side condition and its arithmetic are refuted by
`decide`.  Parser mirrors of every witnessed text (the mapping prefix at column `nv`) and of
the `nv > k` dedent were read by `parseYaml` BEFORE the rows were written. -/
section ValueLandedSeqWitnesses
open L4YAML.Surface L4YAML.CharPredicates L4YAML.Proofs.StreamAccum

/-- `GNot SNsChar` at a line feed: `'\n'` is a break, hence not an ns-char. -/
lemma gnotLf (rest : List Char) (col : Nat) : GNot SNsChar ⟨'\n' :: rest, col⟩ := by
  intro s' h
  cases h with
  | mk c _ _ hp => exact hp.1 (Or.inl (by simp [isLineFeedProp]))

/-- `GNot SNsChar` at a space: white space is not an ns-char. -/
lemma gnotSpace (rest : List Char) (col : Nat) : GNot SNsChar ⟨' ' :: rest, col⟩ := by
  intro s' h
  cases h with
  | mk c _ _ hp => exact hp.2.1 (Or.inl (by simp [isSpaceProp]))

/-- `GNot SNsChar` at end of input: no character matches. -/
lemma gnotEof (col : Nat) : GNot SNsChar ⟨[], col⟩ := fun _ h => nomatch h

/-- `s-l-comments` across a line feed at ANY column (generalizes `sslBreak1`). -/
lemma sslBreakAt (rest : List Char) (col : Nat) : SSLComments ⟨'\n' :: rest, col⟩ ⟨rest, 0⟩ :=
  SSLComments.withComment _ _ _ (SSBComment.noSep _ _ (SBComment.break _ _ (SBBreak.lf rest col)))
    (GStar.nil _)

/-- `s-l-comments` at end of input: the `eof` comment, zero width. -/
lemma sslEof (col : Nat) : SSLComments ⟨[], col⟩ ⟨[], col⟩ :=
  SSLComments.withComment _ _ _ (SSBComment.noSep _ _ (SBComment.eof col)) (GStar.nil _)

/-- W1 — the EMPTY entry `-⏎` at column 0: `[183]` with `k = 0`, ending at the next line start. -/
lemma entriesDash : SBlockSeqEntries 0 ⟨['-', '\n'], 0⟩ ⟨[], 0⟩ :=
  SBlockSeqEntries.single 0 _ ⟨['-', '\n'], 0⟩ ⟨['\n'], 1⟩ ⟨[], 0⟩ _ (SIndent.zero _)
    (GLit.mk ['\n'] 0) (gnotLf [] 1) (SBlockIndented.empty 0 .blockIn _ _ (sslBreakAt [] 1))

/-- W1 applied: `valueLandedSeq` at `nv = k = 0` — the `a:⏎-⏎` value, `SBlockNode 1 .blockOut`
    over exactly the entry's characters. -/
lemma valueDash : SBlockNode 1 .blockOut ⟨['-', '\n'], 0⟩ ⟨[], 0⟩ :=
  valueLandedSeq (nv := 0) (k := 0) (Nat.le_refl 0)
    (SSLComments.startOfLine _ _ (GStar.nil _)) entriesDash

/-- W2 — TWO entries `-⏎-⏎` (`cons` onto W1). -/
lemma entriesDashDash : SBlockSeqEntries 0 ⟨['-', '\n', '-', '\n'], 0⟩ ⟨[], 0⟩ :=
  SBlockSeqEntries.cons 0 _ ⟨['-', '\n', '-', '\n'], 0⟩ ⟨['\n', '-', '\n'], 1⟩ ⟨['-', '\n'], 0⟩ _
    (SIndent.zero _) (GLit.mk ['\n', '-', '\n'] 0) (gnotLf ['-', '\n'] 1)
    (SBlockIndented.empty 0 .blockIn _ _ (sslBreakAt ['-', '\n'] 1)) entriesDash

/-- W2 applied: the node spans both entries, ending where the second does. -/
lemma valueDashDash : SBlockNode 1 .blockOut ⟨['-', '\n', '-', '\n'], 0⟩ ⟨[], 0⟩ :=
  valueLandedSeq (nv := 0) (k := 0) (Nat.le_refl 0)
    (SSLComments.startOfLine _ _ (GStar.nil _)) entriesDashDash

/-- W3 — the PUSHED entry ` -⏎` (`k = 1`): `s-indent(1)` then the dash. -/
lemma entriesIndDash : SBlockSeqEntries 1 ⟨[' ', '-', '\n'], 0⟩ ⟨[], 0⟩ :=
  SBlockSeqEntries.single 1 _ ⟨['-', '\n'], 1⟩ ⟨['\n'], 2⟩ ⟨[], 0⟩ _
    (SIndent.succ 0 ['-', '\n'] 0 _ (SIndent.zero _)) (GLit.mk ['\n'] 1) (gnotLf [] 2)
    (SBlockIndented.empty 1 .blockIn _ _ (sslBreakAt [] 2))

/-- W3 applied at `nv = 0 < k = 1` (`a:⏎ -⏎`, the pushed case): `SBlockNode 1 .blockOut`. -/
lemma valueIndDashPushed : SBlockNode 1 .blockOut ⟨[' ', '-', '\n'], 0⟩ ⟨[], 0⟩ :=
  valueLandedSeq (nv := 0) (k := 1) (Nat.zero_le 1)
    (SSLComments.startOfLine _ _ (GStar.nil _)) entriesIndDash

/-- W3 applied at `nv = k = 1` (` a:⏎ -⏎`, the mapping at column 1): the SAME entries are the
    value of a mapping one column over — `SBlockNode 2 .blockOut`, same endpoint. -/
lemma valueIndDashOwn : SBlockNode 2 .blockOut ⟨[' ', '-', '\n'], 0⟩ ⟨[], 0⟩ :=
  valueLandedSeq (nv := 1) (k := 1) (Nat.le_refl 1)
    (SSLComments.startOfLine _ _ (GStar.nil _)) entriesIndDash

/-- W4 — a NESTED compact entry `- -⏎`: the outer entry's node is `[185]`'s `compactSeq` at
    `m = 1`, its inner `[183]` at index `0 + 1 + 1 = 2`. -/
lemma entriesNested : SBlockSeqEntries 0 ⟨['-', ' ', '-', '\n'], 0⟩ ⟨[], 0⟩ :=
  SBlockSeqEntries.single 0 _ ⟨['-', ' ', '-', '\n'], 0⟩ ⟨[' ', '-', '\n'], 1⟩ ⟨[], 0⟩ _
    (SIndent.zero _) (GLit.mk [' ', '-', '\n'] 0) (gnotSpace ['-', '\n'] 1)
    (SBlockIndented.compactSeq 0 .blockIn 1 _ ⟨['-', '\n'], 2⟩ _
      (SIndent.succ 0 ['-', '\n'] 1 _ (SIndent.zero _))
      (SCompactSeq.mk 2 _ ⟨['\n'], 3⟩ ⟨[], 0⟩ _ (GLit.mk ['\n'] 2) (gnotLf [] 3)
        (SBlockIndented.empty 2 .blockIn _ _ (sslBreakAt [] 3)) (SCompactSeqTail.nil 2 _)))

/-- W4 applied at `nv = k = 0`: the node spans the nested entry too. -/
lemma valueNested : SBlockNode 1 .blockOut ⟨['-', ' ', '-', '\n'], 0⟩ ⟨[], 0⟩ :=
  valueLandedSeq (nv := 0) (k := 0) (Nat.le_refl 0)
    (SSLComments.startOfLine _ _ (GStar.nil _)) entriesNested

/-- W5 — an entry closed by END OF INPUT, `-` with no break: the endpoint is `⟨[], 1⟩`, the
    entry's own column, NOT a line start. -/
lemma entriesDashEof : SBlockSeqEntries 0 ⟨['-'], 0⟩ ⟨[], 1⟩ :=
  SBlockSeqEntries.single 0 _ ⟨['-'], 0⟩ ⟨[], 1⟩ ⟨[], 1⟩ _ (SIndent.zero _)
    (GLit.mk [] 0) (gnotEof 1) (SBlockIndented.empty 0 .blockIn _ _ (sslEof 1))

/-- W5 applied: the node ends at column 1 of the exhausted input. -/
lemma valueDashEof : SBlockNode 1 .blockOut ⟨['-'], 0⟩ ⟨[], 1⟩ :=
  valueLandedSeq (nv := 0) (k := 0) (Nat.le_refl 0)
    (SSLComments.startOfLine _ _ (GStar.nil _)) entriesDashEof

/-- The `nv > k` corner is REFUTED, not instantiated: no `hnk`, and the arithmetic the proof
    rewrites through is false (`seqSpaces 2 .blockOut + (0 - 1) = 1 ≠ 0`, `3 .blockOut + (1 - 2) = 2 ≠ 1`). -/
example : ¬ (1 ≤ 0) ∧ ¬ (2 ≤ 1) := by decide
example : seqSpaces (1 + 1) .blockOut + (0 - 1) ≠ 0 ∧ seqSpaces (2 + 1) .blockOut + (1 - 2) ≠ 1 := by
  decide

/-- The five conclusions, named together so a destructuring failure cannot hide one (§7). -/
example : SBlockNode 1 .blockOut ⟨['-', '\n'], 0⟩ ⟨[], 0⟩ ∧
    SBlockNode 1 .blockOut ⟨['-', '\n', '-', '\n'], 0⟩ ⟨[], 0⟩ ∧
    SBlockNode 1 .blockOut ⟨[' ', '-', '\n'], 0⟩ ⟨[], 0⟩ ∧
    SBlockNode 2 .blockOut ⟨[' ', '-', '\n'], 0⟩ ⟨[], 0⟩ ∧
    SBlockNode 1 .blockOut ⟨['-', ' ', '-', '\n'], 0⟩ ⟨[], 0⟩ ∧
    SBlockNode 1 .blockOut ⟨['-'], 0⟩ ⟨[], 1⟩ :=
  ⟨valueDash, valueDashDash, valueIndDashPushed, valueIndDashOwn, valueNested, valueDashEof⟩

end ValueLandedSeqWitnesses

/-- Priority 59, Rule 2 for item 388 — the mapping park's value route typed `.blockOut` (the
    grammar's `[187]` context, `SBlockMapEntry.implicitKeyNode`) and `valueLandedSeq`: a `-` at the
    enclosing mapping's OWN column is that mapping's VALUE (`[185]` `seq-spaces(n + 1, block-out) =
    n`), not a bare root node.  Parser rows (verdict + documents; §7: they cannot see which route
    fired — the route's informative side is the frame-list pin `RelaySupplyCensus` and the
    `h_seqBottom` leaf of `OpenerFallbackReach`): the no-push `-` under an EMPTY `a:` is one
    document on every row; after a FILLED value (`a: 1⏎- b`) or under `? a` it is refused; a
    document end (`...`) makes two.  Lemma rows: `valueLandedSeq`'s side condition `nv ≤ k` read as
    the `seqSpaces` arithmetic it discharges (`seqSpaces (nv + 1) .blockOut + (k - nv) = k`) beside
    `nestedBlockSeq`'s `.blockIn` twin (`seqSpaces (nv + 1) .blockIn + (k - (nv + 1)) = k` iff
    `nv + 1 ≤ k`): the one column the `.blockIn` typing cost, over `nv, k ∈ 0..3`.  All 16 parser
    verdicts were read by `parseYaml` before the rows were written; the lemma rows predict 10 of 16
    `(nv, k)` pairs in `.blockOut`'s domain and 6 in `.blockIn`'s. -/
def testValueLandedSeq (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 59: item 388 — a `-` at the mapping's own column is the mapping's VALUE ([185] seq-spaces, .blockOut): parser verdicts + documents on the no-push rows; valueLandedSeq's nv ≤ k beside nestedBlockSeq's nv + 1 ≤ k"
  let rows : List (String × String × Option Nat) :=
    [ ("a:⏎- b (the value: one document)", "a:\n- b", some 1),
      ("a:⏎-⏎c: 1 (the mapping's sibling after the empty entry)", "a:\n-\nc: 1", some 1),
      ("a:⏎- b⏎- c⏎d: 1 (two entries, then the sibling)", "a:\n- b\n- c\nd: 1", some 1),
      ("a:⏎  b:⏎  -⏎  c: 1 (one level down)", "a:\n  b:\n  -\n  c: 1", some 1),
      ("- a:⏎  -⏎  c: 1 (inside a sequence entry's mapping)", "- a:\n  -\n  c: 1", some 1),
      ("-⏎c: 1 (a bare root `-`: no mapping — refused, trailing content)", "-\nc: 1", none),
      ("a:⏎-⏎? c (the sibling as an explicit key)", "a:\n-\n? c", some 1),
      ("a:⏎-⏎: v (the sibling as an empty key)", "a:\n-\n: v", some 1),
      ("a: &x⏎- b⏎c: 1 (properties on the value line)", "a: &x\n- b\nc: 1", some 1),
      ("a: # c⏎- b⏎c: 1 (a comment on the value line)", "a: # c\n- b\nc: 1", some 1),
      ("a:⏎- b⏎...⏎c: 1 (a document end between: two documents)", "a:\n- b\n...\nc: 1", some 2),
      ("? a⏎-⏎c: 1 (under an explicit KEY the `-` is bare document content — refused)", "? a\n-\nc: 1", none),
      ("a:⏎-⏎  c: 1 (the entry's own node, deeper)", "a:\n-\n  c: 1", some 1),
      ("a:⏎ -⏎c: 1 (the pushed case nv < k, then the dedent sibling)", "a:\n -\nc: 1", some 1),
      ("a: 1⏎- b (after a FILLED value: bare document content — refused)", "a: 1\n- b", none),
      ("a:⏎- b⏎  c: 1 (a deeper `c:` continues the plain scalar: invalid implicit key)", "a:\n- b\n  c: 1", none) ]
  for (label, input, expected) in rows do
    let got : Option Nat := match L4YAML.TokenParser.parseYaml input with
      | .ok d => some d.size | .error _ => none
    checkM state s!"P59 {label}: documents = {repr expected}" (got == expected) s!"got {repr got}"
  let mut outDom := 0
  let mut inDom := 0
  for nv in [0, 1, 2, 3] do
    for k in [0, 1, 2, 3] do
      let outOk := L4YAML.Surface.seqSpaces (nv + 1) .blockOut + (k - nv) == k
      let inOk := L4YAML.Surface.seqSpaces (nv + 1) .blockIn + (k - (nv + 1)) == k
      if outOk then outDom := outDom + 1
      if inOk then inDom := inDom + 1
      checkM state s!"P59 valueLandedSeq side condition nv={nv} k={k}: seqSpaces arithmetic ↔ nv ≤ k"
        (outOk == decide (nv ≤ k)) s!"outOk={outOk}"
      checkM state s!"P59 nestedBlockSeq (.blockIn) twin nv={nv} k={k}: arithmetic ↔ nv + 1 ≤ k"
        (inOk == decide (nv + 1 ≤ k)) s!"inOk={inOk}"
  checkM state s!"P59 domains: .blockOut pairs = {outDom} (predicted 10), .blockIn pairs = {inDom} (predicted 6)"
    (outDom == 10 && inDom == 6) s!"{outDom}/{inDom}"
  -- Priority 59b: the witnessed texts, mirrored at the parser with the mapping prefix at column
  -- `nv` (verdicts read by `parseYaml` before the rows were written); the `nv > k` corner's
  -- mirror (`  a:⏎-⏎`, k = 0 < nv = 2) is the dedent the parser refuses.
  let wit : List (String × String × Nat × Nat × Nat × Option Nat) :=
    [ ("W1 -⏎ (valueDash)", "-\n", 0, 0, 0, some 1),
      ("W2 -⏎-⏎ (valueDashDash)", "-\n-\n", 0, 0, 0, some 1),
      ("W3 ␣-⏎ pushed (valueIndDashPushed)", " -\n", 0, 1, 0, some 1),
      ("W3 ␣-⏎ own column (valueIndDashOwn)", " -\n", 1, 1, 0, some 1),
      ("W4 - -⏎ nested (valueNested)", "- -\n", 0, 0, 0, some 1),
      ("W5 - at EOF (valueDashEof)", "-", 0, 0, 1, some 1),
      ("nv > k: ␣␣a:⏎-⏎ REFUTED (no witness; trailing content)", "-\n", 2, 0, 0, none) ]
  let mut built := 0
  for (label, text, nv, k, endCol, expected) in wit do
    let input := String.ofList (List.replicate nv ' ') ++ "a:\n" ++ text
    let got : Option Nat := match L4YAML.TokenParser.parseYaml input with
      | .ok d => some d.size | .error _ => none
    let sideOk := decide (nv ≤ k)
    if sideOk then built := built + 1
    checkM state s!"P59b {label}: nv={nv} k={k} endCol={endCol} side={sideOk} parser documents = {repr expected}"
      (got == expected && (sideOk == expected.isSome)) s!"got {repr got}"
  checkM state s!"P59b witnesses built = {built} (predicted 6: W1, W2, W3×2, W4, W5)" (built == 6) s!"{built}"

/-! ## Priority 60 — item 389: the mapping-top sibling at the `-` park PAID through a conjunct

    The `-` park's `k = n` mapping-top arm now routes the enclosing mapping's sibling from a
    conjunct inside `h_closeF` (`a:⏎- b⏎- c⏎d: 1` reaches `d` through the `-` park, its content
    twin and the pushed/no-push births).  Parser verdicts were read BEFORE the rows were written
    (`scratch`-probe, 10 inputs): every input but `a: 1⏎- b` is accepted; that one is refused by
    `scanBlockEntryValidate` (`invalidBareDocument` at the dash, line 1 col 0), the refuser item 388
    could not name.  P8 (`a:⏎- b⏎ - c`) was predicted REFUSED and read ACCEPTED: the deeper `-` is a
    plain-scalar continuation (`"b - c"`), a reader-side correction recorded in its label.

    Rule 2 for the new stack lemmas (`popStep_lt`, `unwindIndentsLoop_shrink_lt`,
    `preprocess_indents_eq_of_le`): computed on concrete monotone stacks — a pop lowers the top
    strictly, an unwind that shrinks the stack lowers it, an unwind that does not shrink keeps it. -/

def testMapTopSibling (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 60: item 389 — the mapping-top sibling at the `-` park routed through h_closeF's conjunct: parser verdicts + root keys; popStep/unwind on concrete stacks"
  let rows : List (String × String × Option (Nat × List String × List String)) :=
    [ ("P1 a:⏎- b⏎- c⏎d: 1 — sibling after two no-push entries (the paid route)", "a:\n- b\n- c\nd: 1\n", some (1, ["a", "d"], ["b", "c"])),
      ("P2 a: 1⏎- b — CLOSED content park, REFUSED by scanBlockEntryValidate", "a: 1\n- b\n", none),
      ("P3 ? - a⏎: b — `:` on a sequence top (the one input still declined at the site)", "? - a\n: b\n", some (1, ["<non-scalar>"], [])),
      ("P4 a:⏎  - x⏎  - y — pushed `-` then its no-push sibling (landed nv < k)", "a:\n  - x\n  - y\n", some (1, ["a"], ["x", "y"])),
      ("P5 a:⏎- b⏎d: 1 — sibling after one no-push entry (landed nv = k, from h_valF)", "a:\n- b\nd: 1\n", some (1, ["a", "d"], ["b"])),
      ("P6 a:⏎- &x b⏎- c⏎d: 1 — props-decorated entry (props park: conjunct NOT relayed, 12/101 rung)", "a:\n- &x b\n- c\nd: 1\n", some (1, ["a", "d"], ["b", "c"])),
      ("P7 - a⏎- b — root sequence (root birth: pushed, refuted)", "- a\n- b\n", some (1, [], [])),
      ("P8 a:⏎- b⏎ - c — predicted REFUSED, read ACCEPTED: plain-scalar continuation", "a:\n- b\n - c\n", some (1, ["a"], ["b - c"])),
      ("P9 a:⏎- b⏎- c — two no-push entries, no sibling", "a:\n- b\n- c\n", some (1, ["a"], ["b", "c"])),
      ("P10 a:⏎- - b⏎- c⏎d: 1 — compact nested entry (compact birth: pushed, refuted)", "a:\n- - b\n- c\nd: 1\n", some (1, ["a", "d"], ["<non-scalar>", "c"])) ]
  for (label, input, expected) in rows do
    let got := rootKeys input
    checkM state s!"P60 {label}: {repr expected}" (got == expected) s!"got {repr got}"
  -- Rule 2 on the stack lemmas: concrete monotone stacks.
  let mkS (ids : Array L4YAML.Scanner.IndentEntry) : L4YAML.Scanner.ScannerState :=
    { L4YAML.Scanner.ScannerState.mk' "" with indents := ids }
  let sent : L4YAML.Scanner.IndentEntry := { column := -1, isSequence := false }
  let s3 := mkS #[sent, { column := 0, isSequence := false }, { column := 2, isSequence := true }]
  let s2 := mkS #[sent, { column := 0, isSequence := false }]
  let s1 := mkS #[sent]
  checkM state "P60 popStep_lt: [sent, 0 map, 2 seq] → pop → top 0 < 2" ((L4YAML.Proofs.StreamAccum.popStep s3).currentIndent == 0 && s3.currentIndent == 2) s!"{(L4YAML.Proofs.StreamAccum.popStep s3).currentIndent}"
  checkM state "P60 popStep_lt: [sent, 0 map] → pop → top -1 < 0" ((L4YAML.Proofs.StreamAccum.popStep s2).currentIndent == -1) s!"{(L4YAML.Proofs.StreamAccum.popStep s2).currentIndent}"
  checkM state "P60 popStep_lt failed hypothesis: [sent] has size 1 — pop empties, top -1 ≮ -1" ((L4YAML.Proofs.StreamAccum.popStep s1).currentIndent == -1) s!"{(L4YAML.Proofs.StreamAccum.popStep s1).currentIndent}"
  let u0 := L4YAML.Scanner.unwindIndents s3 0
  checkM state "P60 unwindIndentsLoop_shrink_lt: unwind [sent,0,2] to col 0 shrinks (3 → 2) and lowers the top 2 → 0" (u0.indents.size == 2 && u0.currentIndent == 0) s!"size {u0.indents.size} top {u0.currentIndent}"
  let u2 := L4YAML.Scanner.unwindIndents s3 2
  checkM state "P60 unwind to col 2 does not shrink: stack and top unchanged (the eq branch of preprocess_indents_eq_of_le)" (u2.indents.size == 3 && u2.currentIndent == 2) s!"size {u2.indents.size} top {u2.currentIndent}"
  let u1 := L4YAML.Scanner.unwindIndents s3 1
  checkM state "P60 unwind [sent,0,2] to col 1 pops the 2 only: top 0 (shrink ⇒ strictly below the old top)" (u1.indents.size == 2 && u1.currentIndent == 0) s!"size {u1.indents.size} top {u1.currentIndent}"

/-! ## Priority 60b — item 389's scanner lemmas read at every pause (PR #161 review)

Priority 60's rows read the parser and the stack operations, not the lemmas' own premises.
Below, every pause of the real scanner is walked (as Priority 58b walks the `:`/`?` dispatches)
and each of item 389's scanner lemmas is CHECKED where its premises hold: `preprocess_currentIndent_le`
(the preprocess step never raises the top), `preprocess_indents_eq_of_le` (a step that does not
lower the top leaves the stack unchanged), `pushedBirth_not_mapTop` (a `-` dispatched with
`currentIndent < col` leaves `⟨col, true⟩` on top), `noPushBirth_indents` (a `-` dispatched with
`col ≤ currentIndent` leaves the stack unchanged) and `dispatchContent_preserves_indents` (the
content arm, the step `contentLanding_indents_eq` reads).  A violation is a build failure. -/

/-- One walk: `(pauses, prepViol, eqViol, pushed, pushViol, noPush, noPushViol, contentViol)`; a pause is
    counted only where `scanNextToken` itself accepts the step, and each dispatcher result's stack is also
    compared with that step's (`pushViol`/`contentViol`). -/
def mapTopLemmaWalk (input : String) (fuel : Nat := 64) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut pauses := 0
  let mut prepViol := 0
  let mut eqViol := 0
  let mut pushed := 0
  let mut pushViol := 0
  let mut noPush := 0
  let mut noPushViol := 0
  let mut contentViol := 0
  let shape : ScannerState → Array (Int × Bool) := fun st => st.indents.map fun e => (e.column, e.isSequence)
  for _ in [:fuel] do
    -- PR #161 review: a dispatch is counted only when the scanner's OWN step on the same
    -- state succeeds (`scanNextToken` = preprocess + the earlier checks + the dispatch), and
    -- the dispatcher's stack is compared with the step's — so every tally is on the accepted path.
    match scanNextToken s, scanNextToken_preprocess s with
    | .ok (some sN), .ok (some (sp, c)) =>
      pauses := pauses + 1
      if !(decide (sp.currentIndent ≤ s.currentIndent)) then prepViol := prepViol + 1
      if decide (s.currentIndent ≤ sp.currentIndent) && shape sp != shape s then eqViol := eqViol + 1
      let sd := if sp.allowDirectives then
        { sp with allowDirectives := false, documentEverStarted := true } else sp
      if c == '-' then
        match scanNextToken_dispatchBlockIndicators sd '-' with
        | .ok (some s') =>
          if shape s' != shape sN then pushViol := pushViol + 1
          if decide (sd.currentIndent < (sd.col : Int)) then
            pushed := pushed + 1
            if s'.indents.back?.map (fun e => (e.column, e.isSequence)) != some ((sd.col : Int), true) then
              pushViol := pushViol + 1
          else
            noPush := noPush + 1
            if shape s' != shape sd then noPushViol := noPushViol + 1
        | _ => pure ()
      else if c != ':' && c != '?' then
        match scanNextToken_dispatchContent sd c with
        | .ok s' => if shape s' != shape sd || shape s' != shape sN then contentViol := contentViol + 1
        | _ => pure ()
      s := sN
    | _, _ => break
  return (pauses, prepViol, eqViol, pushed, pushViol, noPush, noPushViol, contentViol)

def testMapTopLemmaWalk (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 60b: item 389 (PR #161 review) — the scanner lemmas behind the mapping-top pay read at every real pause: preprocess never raises the top and keeps the stack when it does not lower it; a pushed `-` leaves ⟨col, true⟩ on top, a no-push `-` and every content dispatch leave the stack unchanged"
  -- Predicted before the run: every violation counter 0 on every row; (pushed, noPush) as
  -- labelled — a `-` pushes exactly when its column exceeds the current indent (the root
  -- `-` on the sentinel -1, a `-` under a mapping at a deeper column, a compact `- -`'s inner
  -- dash) and pushes nothing at the mapping's own column; the refused `a: 1⏎- b` dispatch is
  -- no accepted pause.  Pause counts are read, not predicted (printed in the message).
  let rows : List (String × String × (Nat × Nat)) :=
    [ ("a:⏎- b⏎- c⏎d: 1 (two no-push entries, the paid route)", "a:\n- b\n- c\nd: 1\n", (0, 2)),
      ("- a⏎- b (root sequence: the first `-` pushes on the sentinel, the second is its sibling)", "- a\n- b\n", (1, 1)),
      ("a:⏎  - x⏎  - y (pushed under the mapping, then its no-push sibling)", "a:\n  - x\n  - y\n", (1, 1)),
      ("a:⏎- - b⏎- c (compact: the outer dash no-push, the inner pushed)", "a:\n- - b\n- c\n", (1, 2)),
      ("a:⏎  b:⏎  - x⏎c: 1 (no-push one level down, then a dedent)", "a:\n  b:\n  - x\nc: 1\n", (0, 1)),
      ("a: 1⏎- b (CLOSED content park: the `-` dispatch is refused — no accepted dispatch)", "a: 1\n- b\n", (0, 0)),
      ("- - a (two pushes on one line)", "- - a\n", (2, 0)),
      ("a:⏎-⏎c: 1 (empty no-push entry, then the mapping's sibling)", "a:\n-\nc: 1\n", (0, 1)),
      ("- a:⏎    b: 1⏎- c (mapping inside a pushed sequence, then the sibling entry)", "- a:\n    b: 1\n- c\n", (1, 1)),
      ("a: 1⏎b: 2 (no indicator at all: content dispatches only)", "a: 1\nb: 2\n", (0, 0)) ]
  for (label, input, expected) in rows do
    let got := mapTopLemmaWalk input
    let (pauses, prepViol, eqViol, pushed, pushViol, noPush, noPushViol, contentViol) := got
    check state s!"item 389 scanner lemmas over {label}: pauses={pauses} prepViol={prepViol} eqViol={eqViol} pushed={pushed} pushViol={pushViol} noPush={noPush} noPushViol={noPushViol} contentViol={contentViol}; expected (pushed, noPush) = {expected}, every violation 0"
      (prepViol == 0 && eqViol == 0 && pushViol == 0 && noPushViol == 0 && contentViol == 0 && (pushed, noPush) == expected)

/-! ## Priority 61 — item 390: the landed `nv < k` NO-PUSH half PRICED and STOPPED (STARVED births)

Item 389 left `accum_block_on_closeThenBlock`'s landed birth under `nv < k` with its push half
refuted (`pushedBirth_not_mapTop`) and its no-push half declined.  Item 390 reads that half as
UNREACHABLE once `h_valF` carries the mapping park's top ABOVE by its level
(`sc.currentIndent ≤ nv`: then `k ≤ s_prep.currentIndent ≤ sc.currentIndent ≤ nv < k`), prices the
conjunct (`flip_valf_top.py --stage 1`, now `scripts/flips/item390_valf_top_stage1.json`: 3 declarations / 10 sites) and the `pendingMapValue` field that
would feed it (`--stage 2`: 10 declarations / 92 sites), and STOPS: two of the six births — the
implicit-key `:` (`colon_open_map_implicit`, `colon_open_map_props`) — have no upper bound on the top
in scope.  The `:` pushes at the KEY's column (`value_key_floor` is the LOWER bound) and nothing in the
tree says a live simple key stands at or right of the current top.

Rows below: (1) the parser at the inputs the half is read against — the second `-` of
`a:⏎  - x⏎  - y` lands on the `-` PARK (Priority 60's `k = n` arm), not on `closeThenBlock`; a `-` at a
filled mapping's own column is refused; a `-` at an awaiting key's column is that key's value
(`nv = k`, not `nv < k`); (2) `liveKeyTopWalk`, the MISSING invariant read at every accepted pause of
the real scanner: at a `:` with a live same-line key behind the cursor, the top is at or left of the
key's column BEFORE and AFTER the dispatch; at a keyless `:`/`?`, the top after is at or left of its
column.  Every violation counter is predicted 0 — the fact is TRUE on every pause read and UNPROVED,
which is what makes the two births STARVED rather than REFUTED.  Verdicts were read before the rows
were written (ledger); three `rootKeys` triples were corrected on the reader (it renders a mapping
value's KEYS and a sequence value's items — item 387's lesson), no verdict moved. -/

def liveKeyTopWalk (input : String) (fuel : Nat := 64) : Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut s := L4YAML.Scanner.ScannerState.mk' input
  let mut pauses := 0
  let mut liveColons := 0
  let mut preViol := 0
  let mut postViol := 0
  let mut keyless := 0
  let mut keylessViol := 0
  for _ in [:fuel] do
    match L4YAML.Scanner.scanNextToken s, L4YAML.Scanner.scanNextToken_preprocess s with
    | .ok (some sN), .ok (some (sp, c)) =>
      pauses := pauses + 1
      if c == ':' && sp.simpleKey.possible && sp.simpleKey.pos.line == sp.line
          && sp.simpleKey.pos.offset != sp.offset then
        liveColons := liveColons + 1
        if !(decide (sp.currentIndent ≤ (sp.simpleKey.pos.col : Int))) then preViol := preViol + 1
        if !(decide (sN.currentIndent ≤ (sp.simpleKey.pos.col : Int))) then postViol := postViol + 1
      else if (c == ':' || c == '?') && !sp.inFlow then
        keyless := keyless + 1
        if !(decide (sN.currentIndent ≤ (sp.col : Int))) then keylessViol := keylessViol + 1
      s := sN
    | _, _ => break
  return (pauses, liveColons, preViol, postViol, keyless, keylessViol)

def testLandedNoPushHalf (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 61: item 390 — the landed nv < k no-push half PRICED and STOPPED: parser verdicts at the half's inputs; the missing upper bound (a live key at or right of the top) read at every accepted pause"
  -- Verdicts read before the rows were written (item 390 ledger): 8/8 HELD; the third component
  -- of R3/R5/R8 corrected on the reader (`rootKeys` renders a mapping value's keys / a sequence's items).
  let rows : List (String × String × Option (Nat × List String × List String)) :=
    [ ("R1 a:⏎  - x⏎  - y — pushed `-`, then its sibling lands on the `-` PARK (not closeThenBlock)", "a:
  - x
  - y
", some (1, ["a"], ["x", "y"])),
      ("R2 a:⏎  b: 1⏎  - y — a `-` at a FILLED mapping's own column: REFUSED (scanBlockEntryValidate)", "a:
  b: 1
  - y
", none),
      ("R3 a:⏎  b:⏎  - y — a `-` at an AWAITING key's column is that key's value (b's park, nv = k)", "a:
  b:
  - y
", some (1, ["a"], ["b"])),
      ("R4 a:⏎  - x⏎  b: 1 — a key on a sequence top: REFUSED", "a:
  - x
  b: 1
", none),
      ("R5 - a:⏎  - y — the compact mapping's own column (nv = k)", "- a:
  - y
", some (1, [], ["a"])),
      ("R6 a:⏎    - x⏎  - y — dedent to a column no stack entry names: REFUSED", "a:
    - x
  - y
", none),
      ("R7 a:⏎  - x⏎c: 1 — pushed `-` then the root sibling", "a:
  - x
c: 1
", some (1, ["a", "c"], ["x"])),
      ("R8 ? a⏎:⏎  - y — explicit value, pushed under the `:` at 0", "? a
:
  - y
", some (1, ["a"], ["y"])) ]
  for (label, input, expected) in rows do
    let got := rootKeys input
    checkM state s!"P61 {label}: {repr expected}" (got == expected) s!"got {repr got}"
  -- The missing invariant, read at every accepted pause: every violation counter 0 (predicted),
  -- (liveColons, keyless) as labelled, pauses read.
  let walks : List (String × String × (Nat × Nat)) :=
    [ ("a:⏎  - x⏎  - y", "a:
  - x
  - y
", (1, 0)),
      ("a: 1⏎b: 2", "a: 1
b: 2
", (2, 0)),
      ("- a:⏎    b: 1⏎- c", "- a:
    b: 1
- c
", (2, 0)),
      ("a:⏎  b:⏎  - y", "a:
  b:
  - y
", (2, 0)),
      ("? a⏎: b (keyless `?` and `:`)", "? a
: b
", (0, 2)),
      ("a:⏎  b: 1⏎c: 2", "a:
  b: 1
c: 2
", (3, 0)),
      ("- - a: 1⏎  - b: 2 (keys inside compact sequences)", "- - a: 1
  - b: 2
", (2, 0)),
      (": x (the empty-key `:` at column 0)", ": x
", (0, 1)),
      ("a: &x b⏎c: !!str d (properties on the values)", "a: &x b
c: !!str d
", (2, 0)),
      ("a:⏎  b:⏎    c: 1⏎  d: 2⏎e: 3 (three levels, two dedents)", "a:
  b:
    c: 1
  d: 2
e: 3
", (5, 0)),
      ("? - a⏎: b (explicit key holding a sequence)", "? - a
: b
", (0, 2)),
      ("- a⏎- b: 1⏎  c: 2 (a mapping inside a sequence entry)", "- a
- b: 1
  c: 2
", (2, 0)) ]
  for (label, input, expected) in walks do
    let (pauses, liveColons, preViol, postViol, keyless, keylessViol) := liveKeyTopWalk input
    check state s!"P61 live-key top bound over {label}: pauses={pauses} liveColons={liveColons} preViol={preViol} postViol={postViol} keyless={keyless} keylessViol={keylessViol}"
      (preViol == 0 && postViol == 0 && keylessViol == 0 && (liveColons, keyless) == expected)

/-! ## Priority 62 — item 392: the second (α) flip PRICED (`flip_root_frame_supply.py`, now `scripts/flips/item392_root_frame_supply_stage{A,B}.json`) and the lever RE-READ

Item 391's NEXT: price the root births SUPPLYING `[FrameLevel.map 0]`.  Stage A (the `ResumeFrames.level`
stagger `<` → `≤` + the three (α) bounds) reads 9 declarations / 21 sites; stage B (A + item 380's 37
frameless births) 16 / 68 = A + item 380's 11 / 47 exactly.  The parser is read here at every input the
(α) lane names — root siblings after a closed value, an empty value, a flow value, a `?` key, a props run,
a marker line, a dedent to a column no stack level holds — so the lane's inputs carry their verdict, not a
recollection.  Verdicts read before the rows were written (item 392 ledger): 10/12 HELD; R6 REFUTED on the
VERDICT (`--- a: 1⏎b: 2` is refused: a block mapping cannot open on the marker line — the marker face at
column 0 has no root-sibling input after a closed value); R8's third component corrected on the reader
(`rootKeys` renders a flow sequence's items). -/

def testRootFrameSupply (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 62: item 392 — the second (α) flip PRICED (stage A 9/21, stage B 16/68 = A + item 380's 11/47) and the lever RE-READ: parser verdicts at every input the (α) lane names"
  let rows : List (String × String × Option (Nat × List String × List String)) :=
    [ ("R1 a: 1⏎b: 2 — the root sibling after a CLOSED value (the eight lines' named input, Priority 44)", "a: 1\nb: 2\n", some (1, ["a", "b"], [])),
      ("R2 a: 1⏎ b: 2 — a sibling at column 1, no stack level: REFUSED", "a: 1\n b: 2\n", none),
      ("R3 a:⏎  b: 1⏎c: 2 — the root sibling after a NESTED mapping (the dedent spends resumeAt at 0)", "a:\n  b: 1\nc: 2\n", some (1, ["a", "c"], ["b"])),
      ("R4 a:⏎  b: 1⏎ c: 2 — dedent to column 1, no stack level: REFUSED", "a:\n  b: 1\n c: 2\n", none),
      ("R5 ? a⏎b: 2 — the root sibling after an explicit key with no value", "? a\nb: 2\n", some (1, ["a", "b"], [])),
      ("R6 --- a: 1⏎b: 2 — a block mapping on the marker line: REFUSED (prediction `accepted` REFUTED; the marker face has no root-sibling input here)", "--- a: 1\nb: 2\n", none),
      ("R7 !!map⏎a: 1⏎b: 2 — the root sibling under a props run at column 0", "!!map\na: 1\nb: 2\n", some (1, ["a", "b"], [])),
      ("R8 a: [1]⏎b: 2 — the root sibling after a FLOW value (the flow park's frames: `flowKeyRoute_of_root`'s hmem arm)", "a: [1]\nb: 2\n", some (1, ["a", "b"], ["1"])),
      ("R9 a: 1⏎---⏎b: 2 — a marker between: TWO documents (the explicit route, not a sibling)", "a: 1\n---\nb: 2\n", some (2, ["a"], [])),
      ("R10 a:⏎b: 2 — the root sibling after an EMPTY value (item 382's resume arm)", "a:\nb: 2\n", some (1, ["a", "b"], [])),
      ("R11 - a: 1⏎  b: 2 — the sibling inside a compact mapping (level 2, not root)", "- a: 1\n  b: 2\n", some (1, [], ["a", "b"])),
      ("R12 a: 1⏎- b — a `-` at the filled mapping's column: REFUSED (item 389's refuser)", "a: 1\n- b\n", none) ]
  for (label, input, expected) in rows do
    let got := rootKeys input
    checkM state s!"P62 {label}: {repr expected}" (got == expected) s!"got {repr got}"

/-! ## Priority 63 — item 393: (α) at the FLOW park PRICED (`flip_flow_frames_field.py`, now `scripts/flips/item393_flow_frames_field.json`) and the site RE-READ

The root sibling after a FLOW value (`a: [1]⏎b: 2`) closes into `PendingNode.pendingFlow`, whose only
route is the stream (`h_stream`): `accum_block_pending`'s `pendingFlow` arm hands `closeThenBlock` every
face as `Or.inr trivial`, so `b` rides `rootMapRoute`.  The rows read the parser at every input the flow
lane names — the value-then-sibling shapes, the root flow then a key (refused: `invalidBareDocument`,
`flowKeyRoute_of_root`'s refutation), the explicit `? [1]` key (paid today through `h_compact_pair`),
the nested park, the column-1 sibling, comments between, trailing content.  Verdicts read before the
rows were written (item 393 ledger, `scratch/p63probe.lean`): 8/8 HELD. -/

def testFlowParkFrames (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 63: item 393 — (α) at the FLOW park PRICED (pendingFlow.h_frF 6/11, born only at block_dispatch_deferred; STARVED until FlowBaseRoutes carries the frames) and the site RE-READ: parser verdicts at every input the flow lane names"
  let rows : List (String × String × Option (Nat × List String × List String)) :=
    [ ("R1 a: [1]⏎b: 2 — the root sibling after a FLOW value (the flow park's live input)", "a: [1]\nb: 2\n", some (1, ["a", "b"], ["1"])),
      ("R2 [1]⏎b: 2 — a root flow then a key: REFUSED (invalidBareDocument; flowKeyRoute_of_root's hmem arm is a refutation)", "[1]\nb: 2\n", none),
      ("R3 a: {x: 1}⏎b: 2 — the same after a flow MAPPING value", "a: {x: 1}\nb: 2\n", some (1, ["a", "b"], ["x"])),
      ("R4 ? [1]⏎: 2⏎b: 3 — the explicit key's flow node (h_compact_pair, paid today)", "? [1]\n: 2\nb: 3\n", some (1, ["<non-scalar>", "b"], [])),
      ("R5 a:⏎  b: [1]⏎  c: 2⏎d: 3 — the nested park: the frames `map 2 :: [map 0]` the face must carry", "a:\n  b: [1]\n  c: 2\nd: 3\n", some (1, ["a", "d"], ["b", "c"])),
      ("R6 a: [1]⏎ b: 2 — a sibling at column 1, no stack level: REFUSED", "a: [1]\n b: 2\n", none),
      ("R7 a: [1] # c⏎b: 2 — comments between the closed value and the sibling (the face's SSLComments)", "a: [1] # c\nb: 2\n", some (1, ["a", "b"], ["1"])),
      ("R8 a: [1]⏎b — a bare scalar after the mapping: REFUSED (trailing content)", "a: [1]\nb\n", none) ]
  for (label, input, expected) in rows do
    let got := rootKeys input
    checkM state s!"P63 {label}: {repr expected}" (got == expected) s!"got {repr got}"

/-! ## Priority 64 — item 394: the flow value's frames CHAIN PAID (`FlowBaseRoutes.valueF`)

Item 393 sited the flow lane's escape at `pendingFlow`; the tree re-read in item 394 sites it at the flow
CLOSE: `accum_step_flow`'s `]`/`}` arms build `PendingNode.pendingContent` with `h_framesS := Or.inr
trivial`, so `accum_block_pending`'s content arm relayed no frames into `closeThenBlock.h_mapF` and the
root sibling `b` of `a: [1]⏎b: 2` rode `rootMapRoute`.  Item 394 adds `FlowBaseRoutes.valueF` (the
value route's frames twin), born at `accum_flow_open_depth0`'s `pendingMapValue` arm from
`pendingMapValue.h_closeF` over `SBlockNode.flowInBlock`, declined (`fun _ _ => Or.inr trivial`) at the
seven other flow-open births, and relayed at both closes into `h_framesS` — so `b` takes the resume arm
on `FrameLevel.map 0 :: ks`.  The rows are Priority 63's eight plus the nested park's dedent the mandate
named (`a:⏎  b: [1]⏎c: 2`) and seven more shapes along the paid chain: a third sibling, the column-1
sibling after a flow MAPPING, a blank line between, two flow values in a row, a nested flow mapping value
before the dedent, a dedent to a column neither mapping holds, and a `-` after the flow value.  Verdicts
read before the rows were written (`scratch/p64probe.lean`, item 394 ledger): 8/8 new rows HELD. -/

def testFlowFramesChain (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 64: item 394 — the flow value's frames chain PAID (FlowBaseRoutes.valueF born at the mapping arm's flow open from h_closeF, relayed at both flow closes into pendingContent.h_framesS): parser verdicts at Priority 63's inputs, the nested park's dedent, and seven more shapes on the paid chain"
  let rows : List (String × String × Option (Nat × List String × List String)) :=
    [ ("R1 a: [1]⏎b: 2 — the root sibling after a FLOW value (now the resume arm on map 0 :: ks)", "a: [1]\nb: 2\n", some (1, ["a", "b"], ["1"])),
      ("R2 [1]⏎b: 2 — a root flow then a key: REFUSED (the root births decline valueF; the scanner refuses the input)", "[1]\nb: 2\n", none),
      ("R3 a: {x: 1}⏎b: 2 — the same after a flow MAPPING value (the `}` close relays too)", "a: {x: 1}\nb: 2\n", some (1, ["a", "b"], ["x"])),
      ("R4 ? [1]⏎: 2⏎b: 3 — the explicit key's flow node (h_compact_pair; the `?` birth declines valueF)", "? [1]\n: 2\nb: 3\n", some (1, ["<non-scalar>", "b"], [])),
      ("R5 a:⏎  b: [1]⏎  c: 2⏎d: 3 — the nested park: valueF carries map 2 :: [map 0]", "a:\n  b: [1]\n  c: 2\nd: 3\n", some (1, ["a", "d"], ["b", "c"])),
      ("R6 a: [1]⏎ b: 2 — a sibling at column 1, no stack level: REFUSED", "a: [1]\n b: 2\n", none),
      ("R7 a: [1] # c⏎b: 2 — comments between the closed value and the sibling (valueF's SSLComments)", "a: [1] # c\nb: 2\n", some (1, ["a", "b"], ["1"])),
      ("R8 a: [1]⏎b — a bare scalar after the mapping: REFUSED (trailing content)", "a: [1]\nb\n", none),
      ("R9 a:⏎  b: [1]⏎c: 2 — the nested park's DEDENT (the mandate's row): the frames list's tail map 0 resumes c", "a:\n  b: [1]\nc: 2\n", some (1, ["a", "c"], ["b"])),
      ("R10 a: [1]⏎b: 2⏎c: 3 — a third sibling after the resumed mapping", "a: [1]\nb: 2\nc: 3\n", some (1, ["a", "b", "c"], ["1"])),
      ("R11 a: {x: 1}⏎ b: 2 — column 1 after a flow MAPPING value: REFUSED", "a: {x: 1}\n b: 2\n", none),
      ("R12 a: [1]⏎⏎b: 2 — a blank line inside the SSLComments run", "a: [1]\n\nb: 2\n", some (1, ["a", "b"], ["1"])),
      ("R13 a: [1, 2]⏎b: [3]⏎c: 2 — two flow values in a row: the chain is born twice", "a: [1, 2]\nb: [3]\nc: 2\n", some (1, ["a", "b", "c"], ["1", "2"])),
      ("R14 a:⏎  b: [1]⏎  c: {y: 2}⏎d: 3 — a nested flow MAPPING value before the dedent", "a:\n  b: [1]\n  c: {y: 2}\nd: 3\n", some (1, ["a", "d"], ["b", "c"])),
      ("R15 a:⏎  b: [1]⏎ c: 2 — a dedent to column 1, held by neither mapping: REFUSED", "a:\n  b: [1]\n c: 2\n", none),
      ("R16 a: [1]⏎- b — a `-` after the flow value at the mapping's column: REFUSED", "a: [1]\n- b\n", none) ]
  for (label, input, expected) in rows do
    let got := rootKeys input
    checkM state s!"P64 {label}: {repr expected}" (got == expected) s!"got {repr got}"

/-! ## Priority 64b — item 394 option B's indent-stack lemmas read on real stacks (PR #166 review)

Option B carries `pendingMapValue.h_closeF`'s cover from the mapping park to the flow opener with no
top fact: `Covered` is anti-monotone in the stack, so it suffices that the preprocess step only POPS.
Three lemmas say so — `unwindIndentsLoop_mem` (every entry the loop leaves was on the incoming
stack, any fuel), `unwindIndents_mem` (the same at the loop's own fuel `s.indents.size`) and
`preprocess_indents_subset` (`scanNextToken_preprocess sc = .ok (some (s_prep, c)) → ∀ e ∈ s_prep.indents,
e ∈ sc.indents`).  Rule 2 below instantiates them where their premises hold: the loop on empty /
singleton / nested stacks at fuel 0, 1, 2 and `size`, against columns below, at and above the top
(vacuous rows — nothing popped — and nonvacuous rows both counted); the preprocess lemma at every
accepted pause of the scanner on inputs with and without an unwind.  A violation is a build failure. -/

/-- One synthetic stack walk: `(rows, viol, popped)` — every `(fuel, col)` pair is one row; `viol`
    counts an entry of the result that was NOT on the incoming stack; `popped` counts the rows that
    actually removed something (the nonvacuous instances). -/
def unwindMemWalk (stack : Array (Int × Bool)) : Nat × Nat × Nat := Id.run do
  let base : ScannerState := { ScannerState.mk' "" with
    indents := stack.map fun (c, b) => ⟨c, b⟩ }
  let shape : ScannerState → Array (Int × Bool) := fun st => st.indents.map fun e => (e.column, e.isSequence)
  let mut rows := 0
  let mut viol := 0
  let mut popped := 0
  let cols : List Int := [-1, 0, 1, 2, 3, 5]
  let fuels : List Nat := [0, 1, 2, base.indents.size]
  for col in cols do
    for fuel in fuels do
      rows := rows + 1
      let s' := unwindIndentsLoop base col fuel
      if (shape s').any (fun e => !(shape base).contains e) then viol := viol + 1
      if s'.indents.size < base.indents.size then popped := popped + 1
    -- `unwindIndents` itself (the loop at `size`)
    rows := rows + 1
    let s'' := unwindIndents base col
    if (shape s'').any (fun e => !(shape base).contains e) then viol := viol + 1
    if s''.indents.size < base.indents.size then popped := popped + 1
  return (rows, viol, popped)

/-- One scanner walk: `(pauses, viol, unwound)` — at every accepted pause the preprocess result's
    stack is checked against the incoming one (`preprocess_indents_subset`); `unwound` counts the
    pauses where the preprocess popped (the nonvacuous instances). -/
def preprocessSubsetWalk (input : String) (fuel : Nat := 64) : Nat × Nat × Nat := Id.run do
  let mut s := ScannerState.mk' input
  let mut pauses := 0
  let mut viol := 0
  let mut unwound := 0
  let shape : ScannerState → Array (Int × Bool) := fun st => st.indents.map fun e => (e.column, e.isSequence)
  for _ in [:fuel] do
    match scanNextToken s, scanNextToken_preprocess s with
    | .ok (some sN), .ok (some (sp, _)) =>
      pauses := pauses + 1
      if (shape sp).any (fun e => !(shape s).contains e) then viol := viol + 1
      if sp.indents.size < s.indents.size then unwound := unwound + 1
      s := sN
    | _, _ => break
  return (pauses, viol, unwound)

def testIndentSubsetLemmas (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 64b: item 394 option B (PR #166 review) — the indent-stack lemmas behind the cover's park → opener transport read on real stacks: unwindIndentsLoop_mem / unwindIndents_mem over empty, singleton and nested stacks at fuel 0, 1, 2 and size; preprocess_indents_subset at every accepted pause with and without an unwind"
  -- Predicted before the run: viol = 0 on every row.  `popped` per stack: the empty and the
  -- singleton stack pop NOTHING at any fuel or column (the loop keeps `size > 1`) — all rows
  -- vacuous; the nested stack pops only at fuel ≥ 1 and col below the top.
  let stacks : List (String × Array (Int × Bool) × Bool) :=
    [ ("empty stack (fuel 0/1/2/0: every row vacuous)", #[], false),
      ("singleton ⟨-1, map⟩ (the sentinel is never popped: every row vacuous)", #[(-1, false)], false),
      ("nested ⟨-1⟩ ⟨0 map⟩ ⟨2 seq⟩ ⟨4 map⟩ (pops below the top at fuel ≥ 1)", #[(-1, false), (0, false), (2, true), (4, false)], true),
      ("two sequences ⟨-1⟩ ⟨0 seq⟩ ⟨2 seq⟩", #[(-1, false), (0, true), (2, true)], true) ]
  for (label, stack, nonvacuous) in stacks do
    let (rows, viol, popped) := unwindMemWalk stack
    check state s!"unwindIndentsLoop_mem / unwindIndents_mem over {label}: rows={rows} viol={viol} popped={popped}"
      (viol == 0 && (if nonvacuous then popped > 0 else popped == 0))
  -- Predicted before the run: viol = 0 at every pause; `unwound` as labelled.
  let inputs : List (String × String × Nat) :=
    [ ("a: 1⏎b: 2 (no unwind at any pause)", "a: 1\nb: 2\n", 0),
      ("a:⏎  b: 1⏎c: 2 (one dedent: one unwound pause)", "a:\n  b: 1\nc: 2\n", 1),
      ("a:⏎  b:⏎    c: 1⏎d: 2 (two levels closed at one pause)", "a:\n  b:\n    c: 1\nd: 2\n", 1),
      ("a: [1]⏎b: 2 (item 394's live input: no unwind)", "a: [1]\nb: 2\n", 0),
      ("a:⏎  b: [1]⏎c: 2 (the nested flow park, then the dedent)", "a:\n  b: [1]\nc: 2\n", 1),
      ("- a⏎- b (sequence siblings: no unwind)", "- a\n- b\n", 0),
      ("a:⏎  - x⏎b: 1 (a pushed sequence closed by the dedent)", "a:\n  - x\nb: 1\n", 1) ]
  for (label, input, expectedUnwound) in inputs do
    let (pauses, viol, unwound) := preprocessSubsetWalk input
    check state s!"preprocess_indents_subset over {label}: pauses={pauses} viol={viol} unwound={unwound}"
      (viol == 0 && unwound == expectedUnwound)

/-! ## Priority 65 — item 398: the live-key-top invariant (item 391 §5) STATED and read at every accepted pause

`LiveKeyTop` as a STATE predicate, not a `:`-site reading (Priority 61 read it only at live colons): (key) in
block context a live simple key saved on the CURRENT line stands at or right of `currentIndent`; (stack)
every key on `simpleKeyStack` saved on the current line likewise (a flow start parks the key there, a flow
end restores it, and `currentIndent` does not move inside flow).  Read after every `scanNextToken` pause.
`armed` counts the pauses where a clause's hypothesis holds, so a row reads theorem-holds, not
failed-hypothesis.  Predicted before the run: viol = 0 on every row; armed > 0 wherever pauses > 0 — REFUTED on two
rows whose only pause is an indicator or a block scalar (no key is ever saved), pinned `armed = 0`.  The
grid: the implicit-key births' inputs, flow keys and stacked keys, `?`/`-` after properties and quoted
scalars (the `-` is the one writer that pushes WITHOUT clearing the key — the states are refused upstream),
dedents, document markers, block scalars, under-indented flow continuation lines. -/

def liveKeyTopOk (s : L4YAML.Scanner.ScannerState) : Bool × Bool := Id.run do
  let keyArmed := s.simpleKey.possible && s.simpleKey.pos.line == s.line
  let keyOk := !keyArmed || decide (s.currentIndent ≤ (s.simpleKey.pos.col : Int))
  let stackArmed := s.simpleKeyStack.any fun k => k.possible && k.pos.line == s.line
  let stackOk := s.simpleKeyStack.all fun k =>
    !(k.possible && k.pos.line == s.line) || decide (s.currentIndent ≤ (k.pos.col : Int))
  let syncOk := s.simpleKeyStack.size == s.flowLevel
  return (keyOk && stackOk && syncOk, keyArmed || stackArmed)

/-- Every accepted pause of the real scanner: `(pauses, violations, armed pauses)`. -/
def liveKeyTopStateWalk (input : String) (fuel : Nat := 128) : Nat × Nat × Nat := Id.run do
  let mut s := L4YAML.Scanner.ScannerState.mk' input
  let mut pauses := 0
  let mut viol := 0
  let mut armed := 0
  for _ in [:fuel] do
    match L4YAML.Scanner.scanNextToken s with
    | .ok (some sN) =>
      pauses := pauses + 1
      let (ok, isArmed) := liveKeyTopOk sN
      if !ok then viol := viol + 1
      if isArmed then armed := armed + 1
      s := sN
    | _ => break
  return (pauses, viol, armed)

def testLiveKeyTopInvariant (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 65: item 398 — the live-key-top invariant (item 391 §5) as a state predicate, read at every accepted scanner pause: block live same-line key and every stacked key at or right of currentIndent"
  -- Predicted before the run: viol = 0 on every row; armed > 0 on every row with pauses > 0 (two rows
  -- refuted that: a `?` or a block-scalar header as the only pause never saves a key — pinned 0).
  -- Pauses per row were read on a scratch walk first and are pinned here (a moved count is a scanner change).
  let inputs : List (String × String × Nat × Bool) :=
    [ ("a: 1 (the implicit key)", "a: 1\n", 3, true),
      ("\"a\" - b (REFUSED: trailing content after a quoted key)", "\"a\" - b\n", 0, false),
      ("&x - b (REFUSED after the anchor's pause: sameLineBlockCollection)", "&x - b\n", 1, true),
      ("!t - b (REFUSED after the tag's pause)", "!t - b\n", 1, true),
      ("*al - b (REFUSED)", "*al - b\n", 0, false),
      ("a: [1] (a flow value)", "a: [1]\n", 5, true),
      ("[a]: b (a flow key: the stacked key clause)", "[a]: b\n", 5, true),
      ("{a: 1}: b", "{a: 1}: b\n", 7, true),
      ("? a⏎: b (explicit key)", "? a\n: b\n", 4, true),
      ("- - a: 1 (two sequence pushes before the key)", "- - a: 1\n", 5, true),
      ("a:⏎  b: 1⏎c: 2 (the dedent)", "a:\n  b: 1\nc: 2\n", 8, true),
      ("\"a\": 1 (a quoted key)", "\"a\": 1\n", 3, true),
      ("- \"a\" - b (REFUSED)", "- \"a\" - b\n", 1, true),
      ("x:⏎  y: [a,⏎b: c] (flow continuation at column 0)", "x:\n  y: [a,\nb: c]\n", 7, true),
      ("x:⏎  y: [a,⏎  b: c] (flow continuation at the key's column)", "x:\n  y: [a,\n  b: c]\n", 7, true),
      ("a # c⏎- b (a comment, then a sequence at the root)", "a # c\n- b\n", 1, true),
      ("a:⏎  - b⏎  - c: d (a mapping inside a sequence entry)", "a:\n  - b\n  - c: d\n", 8, true),
      ("? - a⏎: - b (sequences under an explicit key and its value)", "? - a\n: - b\n", 6, true),
      ("a: &x b: c (REFUSED: a same-line nested key)", "a: &x b: c\n", 4, true),
      ("--- a: 1 (a key on the marker line)", "--- a: 1\n", 2, true),
      ("a: b⏎  c: d (REFUSED: a deeper key after a scalar value)", "a: b\n  c: d\n", 3, true),
      ("k:⏎  \"q\" ? x (REFUSED)", "k:\n  \"q\" ? x\n", 2, true),
      ("a:   # c⏎  b: 1 (a comment on the key line)", "a:   # c\n  b: 1\n", 5, true),
      ("- a: 1⏎  b: 2 (the compact mapping in a sequence entry)", "- a: 1\n  b: 2\n", 7, true),
      ("a: [b, {c: d}]: e (REFUSED: a flow value as a key)", "a: [b, {c: d}]: e\n", 11, true),
      ("[a: b]: c (a flow mapping key)", "[a: b]: c\n", 7, true),
      ("x:⏎  [a,⏎  b]: c (a flow key over two lines)", "x:\n  [a,\n  b]: c\n", 7, true),
      ("x:⏎  [a,⏎b]: c (REFUSED: an under-indented flow line)", "x:\n  [a,\nb]: c\n", 5, true),
      ("&a &b c: d (REFUSED: two anchors)", "&a &b c: d\n", 1, true),
      ("a: 1 - b (a plain scalar containing ` - `)", "a: 1 - b\n", 3, true),
      ("\"a\" ? b (REFUSED)", "\"a\" ? b\n", 0, false),
      ("\"a\": - b (REFUSED: a same-line sequence value)", "\"a\": - b\n", 2, true),
      ("? \"a\" - b (REFUSED at the quoted key: the one pause is the `?`, no key saved)", "? \"a\" - b\n", 1, false),
      ("a:⏎- b (a sequence value at the key's column)", "a:\n- b\n", 4, true),
      ("a:⏎ -b (a plain scalar `-b` at column 1)", "a:\n -b\n", 3, true),
      ("'a' - b (REFUSED)", "'a' - b\n", 0, false),
      ("a:⏎  b: [1,⏎2]⏎  c: 3 (REFUSED: an under-indented flow line)", "a:\n  b: [1,\n2]\n  c: 3\n", 7, true),
      ("|⏎ a⏎- b (REFUSED after the block scalar: its one pause clears the key)", "|\n a\n- b\n", 1, false),
      ("a: >⏎ b⏎- c (a folded value, then a root sequence)", "a: >\n b\n- c\n", 3, true),
      -- Item 399: the `-` after a same-line ALIAS key (an alias saves a simple key; `*al - b` alone is
      -- `undefinedAlias`, so these define the anchor first).  Read on the scratch walk before pinning.
      ("a: &x 1⏎*x - b (REFUSED: sameLineBlockCollection after the alias)", "a: &x 1\n*x - b\n", 4, true),
      ("- &x 1⏎- *x - b (REFUSED)", "- &x 1\n- *x - b\n", 4, true),
      ("a: &x 1⏎k: *x - b (REFUSED)", "a: &x 1\nk: *x - b\n", 6, true),
      ("a: &x 1⏎*x: b (an alias as an implicit key)", "a: &x 1\n*x: b\n", 4, true),
      ("&x a - b (REFUSED after the anchored key's pause)", "&x a - b\n", 2, true),
      ("? &x 1⏎: *x - b (REFUSED)", "? &x 1\n: *x - b\n", 4, true) ]
  for (label, input, expectedPauses, armedExpected) in inputs do
    let (pauses, viol, armed) := liveKeyTopStateWalk input
    check state s!"P65 LiveKeyTop at every pause of {label}: pauses={pauses} viol={viol} armed={armed}"
      (viol == 0 && pauses == expectedPauses && (if armedExpected then armed > 0 else armed == 0))

/-! ## Priority 66 — `l4yaml-fmt` (PR #169 review): the aligner's lemmas read at their boundaries

`L4YAML/Proofs/Output/AlignProofs.lean` feeds capstone 6.16 `format_whitespace_only`:
`applyEditsFrom_filter` / `applyEdits_count_newline` (edit application keeps the non-blank
characters and the line count for ANY edit list — empty, zero-width, reversed, overlapping,
out of range, or over non-blank text), `format_ok_filter` / `format_ok_count_newline` /
`format_ok_scanShape` (a successful `format` is a whitespace-only reformat with the same
tokens and comments) and `minGap_le_gap` (an aligned cell keeps at least `minGap`).  Rule 2
below instantiates them on edit lists the planner never emits, on empty / one-entry / BOM /
CRLF / tab / block-scalar / flow / anchored / commented inputs under every configuration
boundary (`maxCell` 0 and 1, `round` 0, `minGap` 0, both groupings), and on cell lists with
and without outliers.  Idempotence (`format cfg out = .ok out`) is CHECKED here, not proved.
A violation is a build failure. -/

/-- `(rows, viol)` — every edit list below applied to `input`; `viol` counts a result whose
    non-blank characters or line count differ from the input's. -/
def alignEditsWalk (input : String) : Nat × Nat := Id.run do
  let n := input.length
  let mk : Nat → Nat → Nat → L4YAML.Align.Edit := fun a b w => { start := a, stop := b, width := w }
  let lists : List (Array L4YAML.Align.Edit) :=
    [ #[], #[mk 0 0 0], #[mk 0 0 3], #[mk 0 n 1], #[mk n n 2], #[mk (n + 5) (n + 9) 1],
      #[mk 2 1 1], #[mk 1 2 0], #[mk 1 2 4], #[mk 0 1 1, mk 0 1 2], #[mk 1 3 1, mk 2 4 1],
      #[mk 3 2 1, mk 0 1 1], #[mk 0 n 0, mk 0 n 0], #[mk 4 5 2, mk 1 2 2, mk 7 8 0] ]
  let nb := input.toList.filter L4YAML.Align.nonBlank
  let nl := input.toList.count '\n'
  let mut rows := 0
  let mut viol := 0
  for es in lists do
    rows := rows + 1
    let out := L4YAML.Align.applyEdits es input
    if out.toList.filter L4YAML.Align.nonBlank != nb || out.toList.count '\n' != nl then
      viol := viol + 1
  return (rows, viol)

/-- `(viol, ok)` — `format cfg input`; when it succeeds, `viol` counts a broken conjunct of
    `format_whitespace_only` plus a failed idempotence re-run; `ok = false` means `format`
    refused the input (an error is allowed; a wrong success is not). -/
def alignFormatWalk (cfg : L4YAML.Align.AlignConfig) (input : String) : Nat × Bool := Id.run do
  match L4YAML.Align.format cfg input with
  | .error _ => return (0, false)
  | .ok out =>
    let mut viol := 0
    if out.toList.filter L4YAML.Align.nonBlank != input.toList.filter L4YAML.Align.nonBlank then
      viol := viol + 1
    if out.toList.count '\n' != input.toList.count '\n' then viol := viol + 1
    if L4YAML.Align.scanShape out != L4YAML.Align.scanShape input then viol := viol + 1
    match L4YAML.Align.format cfg out with
    | .ok out2 => if out2 != out then viol := viol + 1
    | .error _ => viol := viol + 1
    return (viol, true)

/-- `(rows, viol)` — `minGap_le_gap` at every cell that fits, over cell lists with and without
    outliers and every `maxCell` / `round` / `minGap` boundary. -/
def alignGapWalk : Nat × Nat := Id.run do
  let cellLists : List (List Nat) := [[], [3], [3, 10], [41, 2], [40], [1, 1, 1], [7, 8, 9, 50], [0]]
  let mut rows := 0
  let mut viol := 0
  for cells in cellLists do
    for maxCell in ([0, 1, 20, 40] : List Nat) do
      for round in ([0, 1, 4, 8] : List Nat) do
        for minGap in ([0, 1, 3] : List Nat) do
          match L4YAML.Align.groupTarget cells maxCell round with
          | none => pure ()
          | some t =>
            for c in cells do
              if c ≤ maxCell && minGap ≤ c then
                rows := rows + 1
                if L4YAML.Align.gapWidth true t (c - minGap) minGap < minGap then viol := viol + 1
  return (rows, viol)

def testAlignLemmas (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 66: l4yaml-fmt (PR #169 review) — applyEditsFrom_filter / applyEdits_count_newline on edit lists the planner never emits; format_whitespace_only's three conjuncts plus idempotence on boundary inputs under every configuration boundary; minGap_le_gap on cell lists with and without outliers"
  -- Predicted before the run: viol = 0 on every row (the lemmas are unconditional in the edits).
  let editInputs : List (String × String) :=
    [ ("empty input", ""), ("one char", "a"), ("blanks only", "  \t "),
      ("a: 1 (no newline)", "a: 1"), ("two lines", "a: 1\nbb:  2\n"),
      ("CRLF lines", "a: 1\r\nbb: 2\r\n"), ("tabs between", "a:\t\t1\n") ]
  for (label, input) in editInputs do
    let (rows, viol) := alignEditsWalk input
    check state s!"applyEdits keeps non-blanks and line count on {label}: rows={rows} viol={viol}"
      (viol == 0 && rows == 14)
  -- Predicted before the run: every accepted input satisfies all three conjuncts and is a fixed
  -- point of a second pass; the undefined alias and the bad dedent are refused under every cfg.
  -- Read after the first run: `minGap 0` glues `a:1`, which rescans as one plain scalar, so the
  -- fail-closed re-scan refuses every non-empty input — the guard firing, kept as a row
  -- (the CLI rejects `-s 0` for the same reason).
  let cfgs : List (String × L4YAML.Align.AlignConfig) :=
    [ ("default", {}), ("maxCell 0", { maxCell := 0 }), ("maxCell 1", { maxCell := 1 }),
      ("round 0", { round := 0 }), ("round 8", { round := 8 }), ("minGap 0", { minGap := 0 }),
      ("minGap 3", { minGap := 3 }), ("group run", { grouping := .run }),
      ("round 8 minGap 0 maxCell 1", { maxCell := 1, round := 8, minGap := 0 }) ]
  let inputs : List (String × String × Bool) :=
    [ ("empty", "", true), ("a: 1 (no newline)", "a: 1", true), ("a: 1⏎", "a: 1\n", true),
      ("BOM a: 1⏎bbbb: 2", "\uFEFFa: 1\nbbbb: 2\n", true),
      ("BOM with anchors", "\uFEFFlong_key: &lk 1\nb: *lk\n", true),
      ("tab after colon", "a:\tb\nbb: c\n", true),
      ("CRLF", "a: 1\r\nbb: 2\r\n", true),
      ("anchor and alias", "k: &x 1\nkk: *x\n", true),
      ("tag then anchor", "a: !!str x\nbb: &y !!int 7\n", true),
      ("sequence of mappings", "- a: 1\n  bb: 2\n- ccc: 3\n", true),
      ("literal block", "a: |\n  x  y\nbb: 2\n", true),
      ("folded block after long key", "cmd: >\n  one\n  two\nk: 1\n", true),
      ("flow values", "a: {b: 1}\nlong_key: [1, 2]\n", true),
      ("comments and blank lines", "# c\na: 1 # t\n\nbb: 2\n", true),
      ("key: # comment then nested", "a: # c\n  - 1\nbb: 2\n", true),
      ("quoted with spaces", "a: \"x   y\"\nbb: 'p  q'\n", true),
      ("explicit key", "? a\n: 1\nbb: 2\n", true),
      ("nested mappings", "a:\n  b: 1\n  cc: 2\nd: 3\n", true),
      ("outlier key with short anchor", "a_very_long_key_that_exceeds_the_cap: &b 2\nshort: &a 1\n", true),
      ("undefined alias (refused)", "a: *nope\n", false),
      ("bad dedent (refused)", "a:\n  b: 1\n c: 2\n", false) ]
  for (clabel, cfg) in cfgs do
    for (label, input, accepted) in inputs do
      let (viol, ok) := alignFormatWalk cfg input
      let expectOk := accepted && (cfg.minGap > 0 || input.isEmpty)
      check state s!"format_whitespace_only + idempotence [{clabel}] on {label}: viol={viol} ok={ok}"
        (viol == 0 && ok == expectOk)
  -- Predicted before the run: viol = 0; rows > 0 (the nonvacuous instances exist).
  let (rows, viol) := alignGapWalk
  check state s!"minGap_le_gap over cell lists with and without outliers: rows={rows} viol={viol}"
    (viol == 0 && rows > 0)

/-! ## Priority 67 — item 400: the four input-ahead exports READ before they are stated

The live-key-top invariant's `-` case (items 398/399) closes only from what the cursor PEEKS after
a same-line token that saved a simple key.  Item 399 priced four exports and the owner ruled for
them ("go with (ii)"); this bucket reads each one at every accepted pause BEFORE a lemma is stated:
(a) after a block-context PLAIN scalar on the current line the cursor (past whitespace) peeks
EOF, `:`, `#` or a break — `collectPlainScalar_terminates?`'s stop set (`a - b` is one plain
scalar, so a block `-` is never the follower); (b) after a block-context QUOTED scalar the same
set (`validateTrailingContent`); (d) after a block-context ALIAS the same set (`validateAliasClose`);
(c) after an ANCHOR or TAG on the line `lastTokenIsNodePropertyOnLine` holds, which is the guard
`scanBlockEntry` refuses by.  Flow-context pauses are counted apart (the exports hypothesise
`inFlow = false`; `,` `]` `}` follow there).  A violation is a build failure. -/

/-- One pause's reading: `(class, ok)` — class 0 none / 1 plain / 2 quoted / 3 alias /
    4 property / 5 flow-context (skipped). -/
def inputAheadOk (sN : L4YAML.Scanner.ScannerState) : Nat × Bool :=
  match sN.tokens.back? with
  | none => (0, true)
  | some t =>
    if t.pos.line != sN.line then (0, true)
    else
      let follower := (L4YAML.Scanner.skipWhitespace sN).peek?
      let followerOk := match follower with
        | none => true
        | some c => c == ':' || c == '#' || L4YAML.CharPredicates.isLineBreakBool c
            || !L4YAML.CharPredicates.isPrintableBool c || c == '\uFEFF'
      match t.val with
      | .scalar _ .plain => if sN.inFlow then (5, true) else (1, followerOk)
      | .scalar _ .doubleQuoted => if sN.inFlow then (5, true) else (2, followerOk)
      | .scalar _ .singleQuoted => if sN.inFlow then (5, true) else (2, followerOk)
      | .alias _ => if sN.inFlow then (5, true) else (3, followerOk)
      | .anchor _ => (4, L4YAML.Scanner.lastTokenIsNodePropertyOnLine sN.tokens sN.line)
      | .tag _ _ => (4, L4YAML.Scanner.lastTokenIsNodePropertyOnLine sN.tokens sN.line)
      | _ => (0, true)

/-- `(counts per class 1..5, violations)` over every accepted pause of `input`. -/
def inputAheadWalk (input : String) (fuel : Nat := 128) : Array Nat × Nat := Id.run do
  let mut s := L4YAML.Scanner.ScannerState.mk' input
  let mut counts : Array Nat := #[0, 0, 0, 0, 0, 0]
  let mut viol := 0
  for _ in [:fuel] do
    match L4YAML.Scanner.scanNextToken s with
    | .ok (some sN) =>
      let (cls, ok) := inputAheadOk sN
      counts := counts.modify cls (· + 1)
      if !ok then viol := viol + 1
      s := sN
    | _ => break
  return (counts, viol)

def inputAheadInputs : List String :=
  [ "a: b\n", "a:\n", "a #c\n", "a: b #c\n", "a: b   \n", "a: b", "a", "a - b: c\n", "a: b - c\n",
    "key with spaces: v\n", "a:b: c\n", "a: b:c\n", "a:\n  b: c\n", "a: b\nc: d\n", "a: b\r\nc: d\r\n",
    "\"a\": b\n", "'a' #c\n", "a: \"b\"\n", "a: 'b'  \n", "\"a\"", "\"a\" : b\n", "- \"a\"\n", "\"a\":\n  b: c\n",
    "a: &x b\n*x: c\n", "a: &x b\n*x : c\n", "a: &x b\nk: *x\n", "a: &x b\nk: *x #c\n", "- &x a\n- *x\n",
    "&x a: b\n", "!t a: b\n", "a: !t b\n", "&x !t a: b\n", "- &x a\n", "- !t a\n", "? &x a\n: b\n", "&x\na: b\n",
    "? a\n: b\n", "- a\n", "- a: b\n", "- - a\n", "--- a\n", "a\n...\n", "%YAML 1.2\n---\na: b\n",
    "[a, b]\n", "{a: b}\n", "[a, \"b\", 'c']\n", "a: [b, c]\n", "- [a]\n", "a: &x b\nc: [*x, d]\n", "{a: &x b, c: *x}\n",
    "a: |\n  b\nc: d\n", "a: >\n  b\n", "a: b\n  c\n", "a\n b\n", "\tbad: a\n", "a:\tb\n", "a: b\t#c\n", "a\uFEFF: b\n", "\"a\"\uFEFFb\n" ]

def testInputAheadExports (state : IO.Ref TestCollector) : IO Unit := do
  -- Run 1 (60 rows) predicted plain ≥ 40 / quoted ≥ 10 / alias ≥ 6 / property ≥ 8 / flow ≥ 3: read
  -- 87/8/4/16/16 (quoted, alias REFUTED — the grid holds fewer same-line pauses than guessed).
  -- Run 2 adds the two BOM rows; predicted 88/8/4/16/16, pinned exactly.
  let mut total : Array Nat := #[0, 0, 0, 0, 0, 0]
  for input in inputAheadInputs do
    let (counts, viol) := inputAheadWalk input
    total := (List.range 6).foldl (fun acc i => acc.set! i (acc[i]! + counts[i]!)) total
    check state s!"P67 input-ahead followers at every pause of {repr input}: counts={counts} viol={viol}"
      (viol == 0)
  check state s!"P67 totals plain/quoted/alias/property/flow = {total[1]!}/{total[2]!}/{total[3]!}/{total[4]!}/{total[5]!}"
    (total[1]! == 88 && total[2]! == 8 && total[3]! == 4 && total[4]! == 16 && total[5]! == 16)
  -- 67b — the transport lemmas (`advance_io_congr`, `peek_congr`, `skipTrailingSpaces_peek_congr`,
  -- `TrailingFollower.congr`): at every accepted pause, a twin state with the tokens cleared and
  -- the key flags flipped probes the same follower at fuel 0 / 1 / 2 / full.  Predicted before the
  -- run: viol = 0, rows > 0.
  let mut rows := 0
  let mut viol := 0
  for input in inputAheadInputs do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:128] do
      match L4YAML.Scanner.scanNextToken s with
      | .ok (some sN) =>
        let twin : L4YAML.Scanner.ScannerState :=
          { sN with tokens := #[], simpleKeyAllowed := !sN.simpleKeyAllowed,
                    needIndentCheck := !sN.needIndentCheck }
        for fuel in [0, 1, 2, sN.inputEnd - sN.offset + 1] do
          rows := rows + 1
          let a := (L4YAML.Scanner.skipTrailingSpaces sN fuel).peek?
          let b := (L4YAML.Scanner.skipTrailingSpaces twin fuel).peek?
          if a != b then viol := viol + 1
        if sN.advance.offset != twin.advance.offset || sN.advance.peek? != twin.advance.peek? then
          viol := viol + 1
        s := sN
      | _ => break
  check state s!"P67b skipTrailingSpaces / advance read the input alone: rows={rows} viol={viol}"
    (viol == 0 && rows > 0)

  -- 67c (PR #174 review) — the lemmas' own functions called under their own premises, not read
  -- off `scanNextToken`'s output.  Predicted before the run: at fuel 0 the loop never terminates
  -- (the vacuous arm); at full fuel it always terminates (item 401's obligation, read here);
  -- every `terminated` result stands on `PlainFollower`; `scanBlockEntry` errors at EVERY
  -- same-line-property pause and succeeds at some `-` pause without one; both quoted scans and
  -- the alias close leave a `TrailingFollower` state whenever they succeed.
  let mut t0 := 0;  let mut nt0 := 0   -- fuel 0: terminated / not
  let mut tF := 0;  let mut ntF := 0   -- full fuel: terminated / not
  let mut t12 := 0; let mut nt12 := 0  -- fuel 1, 2
  let mut pviol := 0                   -- terminated result off PlainFollower
  let mut propErr := 0; let mut propOk := 0; let mut dashOk := 0
  let mut qOk := 0; let mut qErr := 0; let mut qViol := 0
  let mut aOk := 0; let mut aErr := 0; let mut aViol := 0
  let plainFollower : L4YAML.Scanner.ScannerState → Bool := fun st =>
    match st.peek? with
    | none => true
    | some c => c == ':' || c == '#' || L4YAML.CharPredicates.isLineBreakBool c
        || !L4YAML.CharPredicates.isPrintableBool c || c == '\uFEFF'
        || (st.col == 0 && L4YAML.Scanner.atDocumentBoundary st)
  let trailingFollower : L4YAML.Scanner.ScannerState → Nat → Bool := fun st ie =>
    match (L4YAML.Scanner.skipTrailingSpaces st (ie - st.offset + 1)).peek? with
    | none => true
    | some c => L4YAML.CharPredicates.isLineBreakBool c || c == '#' || c == ':'
  for input in inputAheadInputs do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    -- the quoted scans at the input's start (an initial state is never a pause)
    for sQ in [L4YAML.Scanner.skipWhitespace s] do
      if sQ.peek? == some '"' then
        match L4YAML.Scanner.scanDoubleQuoted sQ with
        | .ok s' =>
          qOk := qOk + 1
          if !trailingFollower s' sQ.inputEnd then qViol := qViol + 1
        | .error _ => qErr := qErr + 1
      if sQ.peek? == some '\'' then
        match L4YAML.Scanner.scanSingleQuoted sQ with
        | .ok s' =>
          qOk := qOk + 1
          if !trailingFollower s' sQ.inputEnd then qViol := qViol + 1
        | .error _ => qErr := qErr + 1
    for _ in [:128] do
      match L4YAML.Scanner.scanNextToken s with
      | .ok (some sN) =>
        if !sN.inFlow then
          let ci := (max 0 (sN.currentIndent + 1)).toNat
          let full := (sN.inputEnd - sN.offset + 1) * 2
          for fuel in [0, 1, 2, full].eraseDups do
            match L4YAML.Scanner.collectPlainScalarLoop sN "" "" fuel false ci sN.inputEnd with
            | .ok r =>
              if fuel == 0 then
                if r.terminated then t0 := t0 + 1 else nt0 := nt0 + 1
              else if fuel == full then
                if r.terminated then tF := tF + 1 else ntF := ntF + 1
              else
                if r.terminated then t12 := t12 + 1 else nt12 := nt12 + 1
              if r.terminated && !plainFollower r.state then pviol := pviol + 1
            | .error _ => pure ()
          if L4YAML.Scanner.lastTokenIsNodePropertyOnLine sN.tokens sN.line then
            match L4YAML.Scanner.scanBlockEntry sN with
            | .error _ => propErr := propErr + 1
            | .ok _ => propOk := propOk + 1
          let sW := L4YAML.Scanner.skipWhitespace sN
          if sW.peek? == some '"' then
            match L4YAML.Scanner.scanDoubleQuoted sW with
            | .ok s' =>
              qOk := qOk + 1
              if !trailingFollower s' sN.inputEnd then qViol := qViol + 1
            | .error _ => qErr := qErr + 1
          if sW.peek? == some '\'' then
            match L4YAML.Scanner.scanSingleQuoted sW with
            | .ok s' =>
              qOk := qOk + 1
              if !trailingFollower s' sN.inputEnd then qViol := qViol + 1
            | .error _ => qErr := qErr + 1
          match sN.tokens.back? with
          | some t =>
            match t.val with
            | .alias _ =>
              if t.pos.line == sN.line then
                match L4YAML.Scanner.validateAliasClose sN with
                | .ok _ =>
                  aOk := aOk + 1
                  if !trailingFollower sN sN.inputEnd then aViol := aViol + 1
                | .error _ => aErr := aErr + 1
            | _ => pure ()
          | none => pure ()
        s := sN
      | _ => break
  -- The contrast for (c): a fresh block state on `-` with no property on its line is accepted.
  for input in ["- a\n", "-\n", "- - a\n"] do
    match L4YAML.Scanner.scanBlockEntry (L4YAML.Scanner.ScannerState.mk' input) with
    | .ok _ => dashOk := dashOk + 1
    | .error _ => pure ()
  check state s!"P67c collectPlainScalarLoop direct: fuel0 term/not={t0}/{nt0} fuel1,2={t12}/{nt12} full={tF}/{ntF} PlainFollower viol={pviol}"
    (t0 == 0 && nt0 == 189 && tF == 189 && ntF == 0 && t12 == 215 && nt12 == 159 && pviol == 0)
  check state s!"P67c scanBlockEntry direct: same-line property err/ok={propErr}/{propOk}, dash without property ok={dashOk}"
    (propErr == 15 && propOk == 0 && dashOk == 3)
  check state s!"P67c quoted scans direct: ok={qOk} err={qErr} TrailingFollower viol={qViol}"
    (qOk == 8 && qErr == 1 && qViol == 0)
  check state s!"P67c validateAliasClose direct: ok={aOk} err={aErr} TrailingFollower viol={aViol}"
    (aOk == 4 && aErr == 0 && aViol == 0)

  -- Priority 68 (item 401) — the fuel half of export (a) and its helpers, called directly.
  -- Predicted before the run: 0 violations everywhere; the fuel bound's nonvacuous rows are the
  -- fuel-1/2 non-terminated results (159); `scanPlainScalar` accepted ≥ 60 times, every result
  -- on `PlainFollower`; `handleBlockLineBreak` both arms populated.
  let mut fuelViol := 0; let mut fuelRows := 0
  let mut nlRows := 0; let mut nlViol := 0
  let mut hbSome := 0; let mut hbNone := 0; let mut hbViol := 0
  let mut ieViol := 0
  let mut psOk := 0; let mut psErr := 0; let mut psViol := 0
  let plainStart : Char → Bool := fun c =>
    !(c == '-' || c == '?' || c == ':' || c == ',' || c == '[' || c == ']' || c == '{' || c == '}'
      || c == '#' || c == '&' || c == '*' || c == '!' || c == '|' || c == '>' || c == '\'' || c == '"'
      || c == '%' || c == '@' || c == '`' || L4YAML.CharPredicates.isWhiteSpaceBool c
      || L4YAML.CharPredicates.isLineBreakBool c)
  let probePlain : L4YAML.Scanner.ScannerState → Nat × Nat × Nat := fun sP =>
    match sP.peek? with
    | some c =>
      if plainStart c && !sP.inFlow then
        match L4YAML.Scanner.scanPlainScalar sP with
        | .ok s' => (1, 0, if plainFollower s' then 0 else 1)
        | .error _ => (0, 1, 0)
      else (0, 0, 0)
    | none => (0, 0, 0)
  for input in inputAheadInputs do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    let (o, e, v) := probePlain (L4YAML.Scanner.skipWhitespace s)
    psOk := psOk + o; psErr := psErr + e; psViol := psViol + v
    for _ in [:128] do
      match L4YAML.Scanner.scanNextToken s with
      | .ok (some sN) =>
        if !sN.inFlow then
          let ci := (max 0 (sN.currentIndent + 1)).toNat
          let full := (sN.inputEnd - sN.offset + 1) * 2
          for fuel in [0, 1, 2, full].eraseDups do
            match L4YAML.Scanner.collectPlainScalarLoop sN "" "" fuel false ci sN.inputEnd with
            | .ok r =>
              if !r.terminated then
                fuelRows := fuelRows + 1
                if !(fuel ≤ sN.inputEnd - sN.offset) then fuelViol := fuelViol + 1
            | .error _ => pure ()
          match sN.peek? with
          | some c =>
            if L4YAML.CharPredicates.isLineBreakBool c then
              nlRows := nlRows + 1
              let sC := L4YAML.Scanner.consumeNewline sN
              if !(sN.offset < sC.offset && sC.inputEnd == sN.inputEnd) then nlViol := nlViol + 1
              match L4YAML.Scanner.collectPlainScalar_handleBlockLineBreak sN "" ci sN.inputEnd with
              | some (_, s2) =>
                hbSome := hbSome + 1
                if !(sN.offset < s2.offset && s2.inputEnd == sN.inputEnd) then hbViol := hbViol + 1
              | none => hbNone := hbNone + 1
          | none => pure ()
          if (L4YAML.Scanner.skipWhitespace sN).inputEnd != sN.inputEnd
              || (L4YAML.Scanner.skipSpaces sN).inputEnd != sN.inputEnd then ieViol := ieViol + 1
          for fuel in [0, 1, 2, sN.inputEnd - sN.offset + 1] do
            if (L4YAML.Scanner.skipBlankLinesLoop sN 0 fuel sN.inputEnd).snd.inputEnd != sN.inputEnd then
              ieViol := ieViol + 1
          let (o, e, v) := probePlain (L4YAML.Scanner.skipWhitespace sN)
          psOk := psOk + o; psErr := psErr + e; psViol := psViol + v
        s := sN
      | _ => break
  check state s!"P68 fuel bound (fuel ≤ inputEnd − offset when not terminated): rows={fuelRows} viol={fuelViol}"
    (fuelRows > 0 && fuelViol == 0)
  check state s!"P68 consumeNewline / handleBlockLineBreak progress at break pauses: nl={nlRows}/{nlViol} hb some/none/viol={hbSome}/{hbNone}/{hbViol}"
    (nlRows > 0 && nlViol == 0 && hbSome > 0 && hbNone > 0 && hbViol == 0)
  check state s!"P68 inputEnd kept by skipWhitespace / skipSpaces / skipBlankLinesLoop: viol={ieViol}" (ieViol == 0)
  check state s!"P68 scanPlainScalar direct → PlainFollower: ok={psOk} err={psErr} viol={psViol}"
    (psOk > 0 && psViol == 0)
  -- 68b — `LiveKeyTop`'s follower conjunct (`KeyFollower`) at every pause with a live same-line
  -- key in block context, and `validateFlowClose` under its premise.  Run 1 (predicted 0
  -- violations, armed ≥ 100) REFUTED the conjunct as first stated: 11 / 145 — every one a `-`
  -- recording its own position as the live key; the block-entry arm was added.  Run 2 predicted
  -- 0 violations, armed ≥ 145; flow-close probes ≥ 5, every success a `TrailingFollower`.
  let mut kfArmed := 0; let mut kfViol := 0
  let mut fcOk := 0; let mut fcErr := 0; let mut fcViol := 0
  let keyFollower : L4YAML.Scanner.ScannerState → Bool := fun st =>
    L4YAML.Scanner.lastTokenIsNodePropertyOnLine st.tokens st.line ||
    (match st.tokens.back? with
     | some t => (match t.val with | .blockEntry => true | _ => false) && t.pos == st.simpleKey.pos
         && st.simpleKeyAllowed
     | none => false) ||
    (match (L4YAML.Scanner.skipWhitespace st).peek? with
     | none => true
     | some c => c == ':' || c == '#' || L4YAML.CharPredicates.isLineBreakBool c
         || !L4YAML.CharPredicates.isPrintableBool c || c == '\uFEFF')
  let extra : List String := ["[a] - b\n", "{a: 1} - b\n", "a: [x] - b\n", "- [a] - b\n", "[a]: b\n",
    "[a] : b\n", "[a] #c\n- b\n", "[a]\n- b\n", "a: [b, c]: d\n", "? [a]\n: b\n", "? \"a\"\n", "? &x a\n", "- - a\n"]
  for input in inputAheadInputs ++ extra do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:128] do
      match L4YAML.Scanner.scanNextToken s with
      | .ok (some sN) =>
        if !sN.inFlow && sN.simpleKey.possible && sN.simpleKey.pos.line == sN.line then
          kfArmed := kfArmed + 1
          if !keyFollower sN then kfViol := kfViol + 1
        if sN.flowLevel == 0 then
          match sN.tokens.back? with
          | some t =>
            match t.val with
            | .flowSequenceEnd | .flowMappingEnd =>
              match L4YAML.Scanner.validateFlowClose sN with
              | .ok _ =>
                fcOk := fcOk + 1
                if !trailingFollower sN sN.inputEnd then fcViol := fcViol + 1
              | .error _ => fcErr := fcErr + 1
            | _ => pure ()
          | none => pure ()
        s := sN
      | _ => break
  -- 68b (review flag, item 402) — FRESH close states, not the pauses `scanNextToken` already
  -- accepted: the preprocess output at the `]`/`}` is closed by `scanFlowSequenceEnd` /
  -- `scanFlowMappingEnd` directly and `validateFlowClose` is read on it.  Predicted: every
  -- trailing-content row rejected, every allowed follower accepted with a `TrailingFollower`.
  let mut fcFreshRej := 0; let mut fcFreshOk := 0; let mut fcFreshViol := 0; let mut fcFreshMiss := 0
  let freshClose : L4YAML.Scanner.ScannerState → Option (Except L4YAML.ScanError Unit × L4YAML.Scanner.ScannerState) :=
    fun s0 => Id.run do
      let mut s := s0
      for _ in [:128] do
        match L4YAML.Scanner.scanNextToken_preprocess s with
        | .ok (some (sp, ']')) =>
          if sp.flowLevel == 1 then
            let s' := L4YAML.Scanner.scanFlowSequenceEnd sp
            return some (L4YAML.Scanner.validateFlowClose s', s')
        | .ok (some (sp, '}')) =>
          if sp.flowLevel == 1 then
            let s' := L4YAML.Scanner.scanFlowMappingEnd sp
            return some (L4YAML.Scanner.validateFlowClose s', s')
        | _ => pure ()
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) => s := sN
        | _ => return none
      return none
  for input in ["[a] - b\n", "[a] x\n", "[a] [b]\n", "{a: 1} - b\n"] do
    match freshClose (L4YAML.Scanner.ScannerState.mk' input) with
    | some (.error _, _) => fcFreshRej := fcFreshRej + 1
    | some (.ok _, _) => fcFreshViol := fcFreshViol + 1
    | none => fcFreshMiss := fcFreshMiss + 1
  for input in ["[a]: b\n", "[a] #c\n", "[a]\n", "[a]"] do
    match freshClose (L4YAML.Scanner.ScannerState.mk' input) with
    | some (.ok _, s') =>
      fcFreshOk := fcFreshOk + 1
      if !trailingFollower s' s'.inputEnd then fcFreshViol := fcFreshViol + 1
    | some (.error _, _) => fcFreshViol := fcFreshViol + 1
    | none => fcFreshMiss := fcFreshMiss + 1
  check state s!"P68b KeyFollower at every live same-line key pause: armed={kfArmed} viol={kfViol}"
    (kfArmed == 151 && kfViol == 0)
  check state s!"P68b validateFlowClose on FRESH closes: rejected={fcFreshRej} accepted={fcFreshOk} viol={fcFreshViol} missed={fcFreshMiss}"
    (fcFreshRej == 4 && fcFreshOk == 4 && fcFreshViol == 0 && fcFreshMiss == 0)
  check state s!"P68b validateFlowClose direct at block-level flow closes: ok={fcOk} err={fcErr} viol={fcViol}"
    (fcOk == 13 && fcErr == 0 && fcViol == 0)

  -- 68c (review) — `LiveKeyTop.dash_case` under its own premises: at every block-context pause
  -- with a live same-line key whose cursor (past whitespace, the preprocess) peeks `-`, call
  -- `scanBlockEntry` and check the conclusion — the line's last token is a block entry at the
  -- saved key's position — on every success.  Predicted before the run: armed ≥ 1 (the `- - a`
  -- rows), every armed call accepted, 0 conclusion violations; vacuous (live key, no `-`) ≥ 140.
  let mut dcArmed := 0; let mut dcOk := 0; let mut dcErr := 0; let mut dcViol := 0; let mut dcVac := 0
  for input in inputAheadInputs ++ extra ++ ["- - \"a\"\n", "- - - a\n", "- - &x a\n", "a:\n- - b\n"] do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:128] do
      match L4YAML.Scanner.scanNextToken s with
      | .ok (some sN) =>
        if !sN.inFlow && sN.simpleKey.possible && sN.simpleKey.pos.line == sN.line then
          match L4YAML.Scanner.scanNextToken_preprocess sN with
          | .ok (some (sP, '-')) =>
            if !sP.inFlow && sP.simpleKey.possible && sP.simpleKey.pos.line == sP.line then
              dcArmed := dcArmed + 1
              match L4YAML.Scanner.scanBlockEntry sP with
              | .ok _ =>
                dcOk := dcOk + 1
                if sP.simpleKey.pos != sP.currentPos then dcViol := dcViol + 1
              | .error _ => dcErr := dcErr + 1
            else dcVac := dcVac + 1
          | _ => dcVac := dcVac + 1
        s := sN
      | _ => break
  check state s!"P68c dash_case (restated: the live key at a `-` dispatch is the fresh save at the cursor) direct: armed={dcArmed} ok={dcOk} err={dcErr} viol={dcViol} vacuous={dcVac}"
    (dcArmed == 11 && dcOk == 11 && dcErr == 0 && dcViol == 0 && dcVac == 155)

  -- 68d (item 402) — the step `scanNextToken_preserves_LiveKeyTop` under its own premise: at every
  -- accepted pause whose state satisfies `LiveKeyTop` (read by `liveKeyTopOk`), the next accepted
  -- pause must too.  Rows count the premise armed/not; the preprocess's hand-off is read as well
  -- (`PreLKT`'s fourth clause: in block context a saved key with `simpleKeyAllowed` sits at the
  -- cursor).  Predicted before the run: every pause armed (P65 reads 0 violations, so the premise
  -- always holds), 0 step violations, 0 hand-off violations; the initial state satisfies the
  -- invariant on every input (`LiveKeyTop.initial`).
  let mut stArmed := 0; let mut stVac := 0; let mut stViol := 0; let mut hoRows := 0; let mut hoViol := 0
  let mut initViol := 0
  for input in inputAheadInputs ++ extra ++ ["- - \"a\"\n", "- - - a\n", "[a] - b\n", "{a: 1}\n"] do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    if !(liveKeyTopOk s).1 then initViol := initViol + 1
    for _ in [:128] do
      match L4YAML.Scanner.scanNextToken s with
      | .ok (some sN) =>
        if (liveKeyTopOk s).1 then
          stArmed := stArmed + 1
          if !(liveKeyTopOk sN).1 then stViol := stViol + 1
        else stVac := stVac + 1
        match L4YAML.Scanner.scanNextToken_preprocess s with
        | .ok (some (sP, _)) =>
          if !sP.inFlow && sP.simpleKeyAllowed && sP.simpleKey.possible then
            hoRows := hoRows + 1
            if sP.simpleKey.pos != sP.currentPos then hoViol := hoViol + 1
        | _ => pure ()
        s := sN
      | _ => break
  check state s!"P68d the step direct: armed={stArmed} vacuous={stVac} viol={stViol}; preprocess hand-off rows={hoRows} viol={hoViol}; initial viol={initViol}"
    (stArmed == 286 && stVac == 0 && stViol == 0 && hoRows == 164 && hoViol == 0 && initViol == 0)

  -- 68e (item 402, review) — the generic §9 whitespace laws under their OWN premises, with the fuels
  -- as free arguments (fuel 0/1/2 pairs; inputs empty, spaces only, space-then-content, tab, content
  -- first, break, comment, and the EOF state).  States are compared on their observable projection.
  -- Predicted before the run: 0 mismatches on every law; saturation/stop/peek rows with the fuel
  -- premise failing are counted as hypothesis-failed, not as violations.
  let proj (t : L4YAML.Scanner.ScannerState) : String :=
    s!"{t.offset},{t.col},{t.line},{t.inputEnd},{t.allowDirectives},{t.documentEverStarted},{t.indents.size}"
  let mut weStates : Array L4YAML.Scanner.ScannerState := #[]
  let mut cnt : Array Nat := Array.replicate 11 0
  for input in ["", " ", "   ", "  x", "\t x", "x", " \n", "  #c", "\t\t", " - a"] do
    let s0 := L4YAML.Scanner.ScannerState.mk' input
    weStates := weStates.push s0
    weStates := weStates.push (s0.advance)
    weStates := weStates.push { s0 with offset := s0.inputEnd }
  for s in weStates do
    for f in [0, 1, 2, s.inputEnd - s.offset] do
      for g in [0, 1, 2] do
        cnt := cnt.modify 0 (· + 1)
        -- skipWhitespaceLoop_skipSpacesLoop
        let sp := L4YAML.Scanner.skipSpacesLoop s f
        if proj (L4YAML.Scanner.skipWhitespaceLoop s (f + g)) !=
            proj (L4YAML.Scanner.skipWhitespaceLoop sp (f + g - (sp.offset - s.offset))) then
          cnt := cnt.modify 1 (· + 1)
        -- skipWhitespaceLoop_stop (f ≤ g, stopped at f)
        let sf := L4YAML.Scanner.skipWhitespaceLoop s f
        let stopped := match sf.peek? with
          | none => true
          | some c => !L4YAML.CharPredicates.isWhiteSpaceBool c
        if f ≤ g && stopped then
          if proj (L4YAML.Scanner.skipWhitespaceLoop s g) != proj sf then cnt := cnt.modify 6 (· + 1)
        else cnt := cnt.modify 7 (· + 1)
      -- skipTrailingSpaces_eq
      if proj (L4YAML.Scanner.skipTrailingSpaces s f) != proj (L4YAML.Scanner.skipWhitespaceLoop s f) then
        cnt := cnt.modify 2 (· + 1)
      -- skipWhitespaceLoop_ad
      let sa : L4YAML.Scanner.ScannerState := { s with allowDirectives := false, documentEverStarted := true }
      let lhs := L4YAML.Scanner.skipWhitespaceLoop sa f
      let rhs : L4YAML.Scanner.ScannerState :=
        { L4YAML.Scanner.skipWhitespaceLoop s f with allowDirectives := false, documentEverStarted := true }
      if proj lhs != proj rhs || lhs.peek? != rhs.peek? then cnt := cnt.modify 3 (· + 1)
      -- saturation + the peek laws, under `inputEnd - offset ≤ f`
      if s.inputEnd - s.offset ≤ f then
        if proj (L4YAML.Scanner.skipWhitespaceLoop s f) != proj (L4YAML.Scanner.skipWhitespace s) then
          cnt := cnt.modify 4 (· + 1)
        if (L4YAML.Scanner.skipSpacesLoop s f).peek? == some ' ' then cnt := cnt.modify 8 (· + 1)
        match (L4YAML.Scanner.skipWhitespaceLoop s f).peek? with
        | some c => if L4YAML.CharPredicates.isWhiteSpaceBool c then cnt := cnt.modify 8 (· + 1)
        | none => pure ()
        match (L4YAML.Scanner.skipToEndOfLineLoop s f).peek? with
        | some c => if !L4YAML.CharPredicates.isLineBreakBool c then cnt := cnt.modify 8 (· + 1)
        | none => pure ()
        match (L4YAML.Scanner.collectCommentTextLoop s "" f).2.peek? with
        | some c => if !L4YAML.CharPredicates.isLineBreakBool c then cnt := cnt.modify 8 (· + 1)
        | none => pure ()
      else
        cnt := cnt.modify 5 (· + 1)
        cnt := cnt.modify 9 (· + 1)
      -- unwindIndentsLoop_cursor at columns -1 / 0 / 2 on a state with pushed indents
      let pushed : Array L4YAML.Scanner.IndentEntry :=
        (s.indents.push { column := 0, isSequence := false }).push { column := 2, isSequence := true }
      let sI : L4YAML.Scanner.ScannerState := { s with indents := pushed }
      for col in [(-1 : Int), 0, 2, 5] do
        let u := L4YAML.Scanner.unwindIndentsLoop sI col f
        if u.offset != sI.offset || u.input != sI.input || u.inputEnd != sI.inputEnd ||
            u.col != sI.col || u.line != sI.line then
          cnt := cnt.modify 10 (· + 1)
  check state s!"P68e the generic §9 whitespace laws direct: rows={cnt[0]!} sum-law viol={cnt[1]!} trailing-eq viol={cnt[2]!} ad-transfer viol={cnt[3]!} saturate viol={cnt[4]!} (vacuous {cnt[5]!}) stop viol={cnt[6]!} (vacuous {cnt[7]!}) peek-laws viol={cnt[8]!} (vacuous {cnt[9]!}) unwind-cursor viol={cnt[10]!}"
    (cnt[0]! == 360 && cnt[1]! == 0 && cnt[2]! == 0 && cnt[3]! == 0 && cnt[4]! == 0 && cnt[6]! == 0 && cnt[8]! == 0 && cnt[10]! == 0 && cnt[5]! == 35 && cnt[7]! == 177 && cnt[9]! == 35)

  -- 68f (item 402, B fold) — `pendingMapValue.h_top`'s supply at the implicit-key births:
  -- (i) `scanValue_top_le_key` DIRECT on crafted states (live key at column k, top ≤ k: the push
  -- branch k > top, the no-push branch k = top, and the `?`-line clear with an explicit key line);
  -- (ii) `implicit_colon_top_le` at every accepted pause whose preprocess hands a `:` to a live
  -- same-line key BEHIND the cursor in block context: `scanValue` must keep the top ≤ the key's
  -- column.  Predicted before the run: 0 violations on both; (ii) armed > 0.
  let mut sfRows := 0
  let mut sfViol := 0
  for (input, kcol, top) in [("a: 1", 0, -1), ("  b: 2", 2, 0), ("  b: 2", 2, 2), ("x: y", 0, 0), ("- a: 1", 2, 0)] do
    let s0 := L4YAML.Scanner.ScannerState.mk' input
    let ci := input.toList.findIdx (· == ':')
    let kpos : L4YAML.YamlPos := { offset := 0, line := 0, col := kcol }
    let s1 : L4YAML.Scanner.ScannerState :=
      { s0 with offset := ci, col := ci,
                indents := #[{ column := -1, isSequence := false }].push { column := top, isSequence := false },
                simpleKey := { possible := true, tokenIndex := 0, pos := kpos } }
    for ekl in [none, some (0 : Nat)] do
      let s2 := { s1 with explicitKeyLine := ekl }
      if s2.peek? == some ':' && s2.currentIndent ≤ (kcol : Int) then
        sfRows := sfRows + 1
        match L4YAML.Scanner.scanValue s2 with
        | .ok s3 => if !(s3.currentIndent ≤ (kcol : Int)) then sfViol := sfViol + 1
        | .error _ => pure ()
  let mut icArmed := 0
  let mut icViol := 0
  for input in inputAheadInputs ++ ["a: 1\n", "  b:\n    c: 2\n", "- a: 1\n  b: 2\n", "? x\n: y\n", "a:\n  b: 1\n  c: 2\n", "&x a: 1\n", "\"q\": 1\n", "a: &y b: 1\n"] do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:128] do
      match L4YAML.Scanner.scanNextToken s with
      | .ok (some sN) =>
        match L4YAML.Scanner.scanNextToken_preprocess s with
        | .ok (some (sP, ':')) =>
          if sP.simpleKey.possible && sP.simpleKey.pos.line == sP.line && sP.simpleKey.pos.offset != sP.offset
              && !sP.inFlow && sP.currentIndent ≤ (sP.simpleKey.pos.col : Int) then
            let sD : L4YAML.Scanner.ScannerState :=
              if sP.allowDirectives then { sP with allowDirectives := false, documentEverStarted := true } else sP
            match L4YAML.Scanner.scanValue sD with
            | .ok s' =>
              icArmed := icArmed + 1
              if !(s'.currentIndent ≤ (sP.simpleKey.pos.col : Int)) then icViol := icViol + 1
            | .error _ => pure ()
        | _ => pure ()
        s := sN
      | _ => break
  check state s!"P68f h_top's supply: scanValue_top_le_key direct rows={sfRows} viol={sfViol}; implicit_colon_top_le at `:` pauses armed={icArmed} viol={icViol}"
    (sfRows == 10 && sfViol == 0 && icArmed == 56 && icViol == 0)

  -- 68g (item 402, review) — the fold's two other new statements DIRECT: (i) `scanValuePrepare_top_le_key`
  -- on the crafted states above (push branch k > top, no-push branch k = top, with and without an explicit
  -- key line), the premise checked apart from the conclusion; (ii) the two seeds `seed_LiveKeyTop` /
  -- `seed_bom_LiveKeyTop`: `LiveKeyTop` read (`liveKeyTopOk`) on `(mk' input).emit .streamStart` and on
  -- its `consumeBOM`, for inputs with and without a leading BOM, empty and non-empty.  Predicted before the
  -- run: prepare rows = 10, 0 violations; seeds 12 states, 0 violations.
  let mut spRows := 0
  let mut spViol := 0
  let mut spVac := 0
  for (input, kcol, top) in [("a: 1", 0, -1), ("  b: 2", 2, 0), ("  b: 2", 2, 2), ("x: y", 0, 0), ("- a: 1", 2, 0)] do
    let s0 := L4YAML.Scanner.ScannerState.mk' input
    let ci := input.toList.findIdx (· == ':')
    let kpos : L4YAML.YamlPos := { offset := 0, line := 0, col := kcol }
    let s1 : L4YAML.Scanner.ScannerState :=
      { s0 with offset := ci, col := ci,
                indents := #[{ column := -1, isSequence := false }].push { column := top, isSequence := false },
                simpleKey := { possible := true, tokenIndex := 0, pos := kpos } }
    for ekl in [none, some (0 : Nat)] do
      let s2 := { s1 with explicitKeyLine := ekl }
      if s2.simpleKey.possible && !s2.inFlow && s2.currentIndent ≤ (s2.simpleKey.pos.col : Int) then
        spRows := spRows + 1
        if !((L4YAML.Scanner.scanValuePrepare s2).currentIndent ≤ (s2.simpleKey.pos.col : Int)) then
          spViol := spViol + 1
      else spVac := spVac + 1
  let mut seedStates := 0
  let mut seedViol := 0
  let mut seedArmed := 0
  for input in ["", "\uFEFF", "a: 1", "\uFEFFa: 1", "\uFEFF- a", "- a\n"] do
    let sE := (L4YAML.Scanner.ScannerState.mk' input).emit .streamStart
    for sX in [sE, sE.consumeBOM] do
      seedStates := seedStates + 1
      let (ok, armed) := liveKeyTopOk sX
      if !ok then seedViol := seedViol + 1
      if armed then seedArmed := seedArmed + 1
  check state s!"P68g the fold's other statements direct: scanValuePrepare_top_le_key rows={spRows} viol={spViol} (vacuous {spVac}); seed_LiveKeyTop/seed_bom_LiveKeyTop states={seedStates} viol={seedViol} armed={seedArmed}"
    (spRows == 10 && spViol == 0 && spVac == 0 && seedStates == 12 && seedViol == 0 && seedArmed == 0)

/-- Priorities 69/69b (item 404) and 69c (item 405): the `?`-park field's chain domain, its fallback,
and the paid ladder's scanner-side claims — split from `testInputAheadExports` (LCNF compile budget). -/
def testKslotDomain (state : IO.Ref TestCollector) : IO Unit := do
  -- 69 (item 404) — the `?`-park field's DOMAIN shape, read before the flip: `MarkedColsIn sc ns`
  -- says every marked slot's column (`pendingKeys[i] = some _` ⇒ `indents[i].column`) is in `ns`.
  -- A SINGLETON domain `[nv]` for `pendingBlock.h_kslot` is refutable iff some accepted `-` pause
  -- in block context under open `?` frames has two DISTINCT marked columns.  Rows: every accepted
  -- pause whose preprocess hands a `-` to the block dispatcher, on nested-`?` inputs (predicted:
  -- ≥ 1 pause with 2 distinct marked columns) and single-`?` inputs (predicted: none).
  let nestedQ : List String := ["?\n  ? -\n: w\n", "? - ? - a\n  : b\n: c\n", "?\n  ?\n    -\n    - b\n  ? c\n: w\n", "? ? - a\n  : b\n: c\n", "- ? - a\n  : b\n"]
  let singleQ : List String := ["? - a\n: b\n", "?\n  - a\n  - b\n: w\n", "k:\n  ? - a\n  : b\n", "? -\n: w\n"]
  let markedCols (s : L4YAML.Scanner.ScannerState) : List Int := Id.run do
    let mut cols : List Int := []
    for i in [:s.pendingKeys.size] do
      match s.pendingKeys[i]?, s.indents[i]? with
      | some (some _), some e => if !(cols.contains e.column) then cols := e.column :: cols
      | _, _ => pure ()
    return cols
  let mut dashN := 0
  let mut twoN := 0
  let mut dashS := 0
  let mut twoS := 0
  for (inputs, nested) in [(nestedQ, true), (singleQ, false)] do
    for input in inputs do
      let mut s := L4YAML.Scanner.ScannerState.mk' input
      for _ in [:64] do
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          match L4YAML.Scanner.scanNextToken_preprocess s with
          | .ok (some (sP, '-')) =>
            if !sP.inFlow then
              let k := (markedCols sP).length
              if nested then
                dashN := dashN + 1
                if k ≥ 2 then twoN := twoN + 1
              else
                dashS := dashS + 1
                if k ≥ 2 then twoS := twoS + 1
          | _ => pure ()
          s := sN
        | _ => break
  check state s!"P69 the ?-park field's domain shape: nested-? `-` pauses={dashN} with ≥2 marked columns={twoN}; single-? `-` pauses={dashS} with ≥2={twoS}"
    (dashN == 8 && twoN == 5 && dashS == 5 && twoS == 0)

  -- 69b (item 404) — the fallback the lane's round 4 exposes: a mapping-value park that is NOT a
  -- `?` park (`NotQuestionPark`) standing under an OUTER `?` has a mark at the outer column, so
  -- `MarkedColsIn sc [nmv]` (nmv = the park's own level) is false there.  Rows: accepted `-`
  -- pauses in block context whose TOP indent level carries no mark while a lower one does, and
  -- whose marked columns are not all the top column.  Predicted: > 0 such pauses on the
  -- outer-`?`-over-mapping inputs, 0 on inputs with no `?`.
  let outerQ : List String := ["? k:\n    - a\n: w\n", "?\n  k:\n    - a\n    - b\n: w\n", "? - k:\n      - a\n: w\n", "?\n  k: v\n  m:\n    - a\n: w\n"]
  let noQ : List String := ["k:\n  - a\n  - b\n", "- k:\n    - a\n", "a:\n  b:\n    - c\n"]
  let mut fbN := 0
  let mut fbHit := 0
  let mut fbZ := 0
  let mut fbZHit := 0
  for (inputs, outer) in [(outerQ, true), (noQ, false)] do
    for input in inputs do
      let mut s := L4YAML.Scanner.ScannerState.mk' input
      for _ in [:64] do
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          match L4YAML.Scanner.scanNextToken_preprocess s with
          | .ok (some (sP, '-')) =>
            if !sP.inFlow then
              let cols := markedCols sP
              let topUnmarked := match sP.pendingKeys.back? with | some none => true | _ => false
              let topCol := (sP.indents.back?.map (·.column)).getD (-1)
              let offTop := cols.any (· != topCol)
              if outer then
                fbN := fbN + 1
                if topUnmarked && !cols.isEmpty && offTop then fbHit := fbHit + 1
              else
                fbZ := fbZ + 1
                if !cols.isEmpty then fbZHit := fbZHit + 1
          | _ => pure ()
          s := sN
        | _ => break
  check state s!"P69b the NotQuestionPark fallback under an outer ?: `-` pauses={fbN} with an off-level mark={fbHit}; no-? pauses={fbZ} marked={fbZHit}"
    (fbN == 6 && fbHit == 5 && fbZ == 5 && fbZHit == 0)

  -- 69c (item 405) — the PAID ladder's two scanner-side claims, read at every accepted pause of
  -- the Priority 69/69b corpus plus the inputs the item's declines NAME (node properties inside a
  -- `?` key: the props park's explicit-key slot `h_kslotE_k` carries no domain, so its three
  -- content relays decline).  (i) `h_mcstep_ne`: a block dispatch on a char other than `?` marks
  -- no new column — the marked set after the step is a subset of the marked set before it
  -- (predicted: 0 violations).  (ii) `h_mcstep`: a `?` dispatch marks at most the preprocessed
  -- column — the marked set after is a subset of {s_prep.col} ∪ before (predicted: 0 violations).
  -- (iii) the named declines are route narrowings, not refusals: every props-in-`?` input still
  -- scans to its end (predicted: all accepted, ≥ 1 non-`?` block pause each).  REFUTED at one row
  -- before the pin: `? &p - a⏎: w` is REFUSED by the scanner — a node property before a same-line
  -- `-` is export (c) of item 400 (`scanBlockEntry` refutes a same-line property), so that input
  -- never reaches the declined relays; the three props-in-`?` inputs that are accepted are the
  -- narrowed class.  Pinned 3 of 4, with the refused row kept as the negative control.
  let propsQ : List String := ["? &p a\n: w\n", "? !!str a\n: w\n", "? - &p a\n  - y\n: v\n", "? &p - a\n: w\n"]
  let mut neN := 0
  let mut neBad := 0
  let mut qN := 0
  let mut qBad := 0
  let mut propsOk := 0
  for input in nestedQ ++ singleQ ++ outerQ ++ propsQ do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    let mut ended := false
    let mut blockPauses := 0
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken s with
      | .ok (some sN) =>
        match L4YAML.Scanner.scanNextToken_preprocess s with
        | .ok (some (sP, c)) =>
          if !sP.inFlow then
            let before := markedCols sP
            let after := markedCols sN
            if c == '?' then
              qN := qN + 1
              if after.any (fun x => x != (sP.col : Int) && !before.contains x) then qBad := qBad + 1
            else
              neN := neN + 1
              blockPauses := blockPauses + 1
              if after.any (fun x => !before.contains x) then neBad := neBad + 1
        | _ => pure ()
        s := sN
      | .ok none => ended := true; break
      | .error _ => break
    if propsQ.contains input && ended && blockPauses ≥ 1 then propsOk := propsOk + 1
  check state s!"P69c h_mcstep_ne/h_mcstep read at every block pause: non-? pauses={neN} new marks={neBad}; ? pauses={qN} off-column marks={qBad}; props-in-? inputs accepted={propsOk}/{propsQ.length}"
    (neN > 0 && neBad == 0 && qN > 0 && qBad == 0 && propsOk == 3 && propsQ.length == 4)

  -- 69d (item 405, Rule 8 fix) — the PROJECTION `RegisterWitness.markedCols` and its three lemmas
  -- instantiated as statements, not read off a transition.  (i) `markedCols_mem` both ways: the
  -- library projection equals the brute-force marked-column list (`markedColsOf`) on hand-built
  -- states — empty, singleton marked/unmarked, nested, and MISALIGNED arrays (`pendingKeys` longer
  -- than `indents` and shorter) — and at every accepted pause of the Priority 69 corpus
  -- (predicted: 0 mismatches).  (ii) `MarkedColsIn.self`: every marked slot's column is a member
  -- (0 misses).  (iii) `MarkedColsIn.relay`, informative: with a REAL domain `ns` (the marks plus
  -- a stray column) and `P := (· ∈ ns)` the conclusion holds at every member of the projection
  -- (0 violations); negative control: dropping the FIRST mark from `ns` breaks the domain premise
  -- at every marked state (predicted: every nonempty state).  (iv) the head consumers split on
  -- `(markedCols sc).reverse`: the projection lists marks OUTERMOST first, so the most recent
  -- still-marked `?` (the park's own) must be its LAST element at every pause (0 violations,
  -- ≥ 1 nested pause where the list has two entries).
  let base : L4YAML.Scanner.ScannerState := L4YAML.Scanner.ScannerState.mk' ""
  let mk (pks : Array (Option Nat)) (cols : Array Int) : L4YAML.Scanner.ScannerState :=
    { base with pendingKeys := pks, indents := cols.map (fun c => { column := c, isSequence := false }) }
  let hand : List L4YAML.Scanner.ScannerState :=
    [ mk #[] #[], mk #[some 1] #[0], mk #[none] #[0], mk #[none, some 3, some 7] #[0, 2, 4],
      mk #[some 1, some 2, some 3] #[0, 2], mk #[some 5] #[0, 2, 4], mk #[none, none] #[0, 2] ]
  let memOk (s : L4YAML.Scanner.ScannerState) : Bool :=
    L4YAML.Proofs.RegisterWitness.markedCols s == markedColsOf s.pendingKeys s.indentColumns
  let selfOk (s : L4YAML.Scanner.ScannerState) : Bool := Id.run do
    let mc := L4YAML.Proofs.RegisterWitness.markedCols s
    for i in [:s.pendingKeys.size] do
      match s.pendingKeys[i]?, s.indentColumns[i]? with
      | some (some _), some c => if !mc.contains c.toNat then return false
      | _, _ => pure ()
    return true
  let isDomain (s : L4YAML.Scanner.ScannerState) (ns : List Nat) : Bool := Id.run do
    for i in [:s.pendingKeys.size] do
      match s.pendingKeys[i]?, s.indentColumns[i]? with
      | some (some _), some c => if !ns.contains c.toNat then return false
      | _, _ => pure ()
    return true
  let mut memBad := 0
  let mut selfBad := 0
  let mut relayBad := 0
  let mut negN := 0
  let mut negBroke := 0
  let mut states := 0
  for s in hand do
    states := states + 1
    if !memOk s then memBad := memBad + 1
    if !selfOk s then selfBad := selfBad + 1
    let mc := L4YAML.Proofs.RegisterWitness.markedCols s
    let ns := mc ++ [99]
    if !isDomain s ns then relayBad := relayBad + 1
    if mc.any (fun nv => !ns.contains nv) then relayBad := relayBad + 1
    if !mc.isEmpty then
      negN := negN + 1
      if !isDomain s (mc.drop 1) then negBroke := negBroke + 1
  -- (v) the own mark is PRESENT where it must be: the state a block `?` dispatch produces holds
  -- the mark at the dispatched column (predicted: 0 misses) — so (iv)'s `mc.contains q` guard
  -- can only skip pauses AFTER the park's `:` consumed its mark, never a missing own mark.
  let mut lastBad := 0
  let mut lastTwo := 0
  let mut ownN := 0
  let mut ownMiss := 0
  for input in nestedQ ++ singleQ do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    let mut lastQ : Option Nat := none
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken s with
      | .ok (some sN) =>
        let mc := L4YAML.Proofs.RegisterWitness.markedCols sN
        match L4YAML.Scanner.scanNextToken_preprocess s with
        | .ok (some (sP, c)) =>
          if c == '?' && !sP.inFlow then
            lastQ := some sP.col
            ownN := ownN + 1
            if !mc.contains sP.col then ownMiss := ownMiss + 1
        | _ => pure ()
        states := states + 1
        if !memOk sN then memBad := memBad + 1
        if !selfOk sN then selfBad := selfBad + 1
        match lastQ with
        | some q =>
          if mc.contains q then
            if mc.getLast? != some q then lastBad := lastBad + 1
            if mc.length ≥ 2 then lastTwo := lastTwo + 1
        | none => pure ()
        s := sN
      | _ => break
  check state s!"P69d markedCols projection: states={states} markedCols_mem mismatches={memBad} MarkedColsIn.self misses={selfBad} relay violations={relayBad}; negative control broke={negBroke}/{negN}; own mark last at ? pauses: violations={lastBad} two-mark pauses={lastTwo}; own mark present after a ? dispatch: misses={ownMiss}/{ownN}"
    (states > 7 && memBad == 0 && selfBad == 0 && relayBad == 0 && negN > 0 && negBroke == negN && lastBad == 0 && lastTwo > 0 && ownN > 0 && ownMiss == 0)

/-- Priority 70/71: the flow carrier (items 406/407) — split from `testKslotDomain` (LCNF timeout). -/
def testKslotPay (state : IO.Ref TestCollector) : IO Unit := do
  -- 73 (item 409) — `MarkedColsIn.step_value` as a STATEMENT: a block-context `:` dispatch adds no mark,
  -- so every mark after the `:` was a mark before it (`MarkedColsIn` is a COVER: the chain at the park
  -- still covers the state after the `:`); negative control: a block `?` dispatch adds its own mark.
  let mut cPauses := 0
  let mut cBad := 0
  let mut cShrink := 0
  let mut qPauses := 0
  let mut qGrow := 0
  -- hypothesis buckets (Rule 2): `step_value` wants `Sound sc`, `Mono sc` and `MarkedColsIn sc ns`
  -- at the PRE-state — count the pauses where they hold (eligible), read the conclusion for the
  -- chain `markedCols s` AND a strict superset cover, and refute the domain's vacuity: `[]`
  -- is NOT a cover at a marked pause.
  let mut cEligible := 0
  let mut cIneligible := 0
  let mut cSuperBad := 0
  let mut cEmptyNotCover := 0
  let coverB (s : ScannerState) (ns : List Nat) : Bool :=
    (L4YAML.Proofs.RegisterWitness.markedCols s).all (fun c => ns.contains c)
  let corpus : List String :=
    ["a: 1\n", "a: [1, 2]\n", "? a\n: b\n", "- ? a: 1\n  : b\n", "? ? a\n  : b\n: c\n", "? - a\n  - b\n: c\n",
     "a:\n  ? b\n  : c\n", "? [a]: b\n: c\n", "? a\n? b\n: c\n", "k: ? a\n   : b\n", "? &p a: b\n: - w\n",
     "- a: 1\n  b: 2\n", "? a\n:\n  - b\n", "{a: 1}\n", "? {a: 1}\n: 2\n"]
  for input in corpus do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          let before := L4YAML.Proofs.RegisterWitness.markedCols s
          let after := L4YAML.Proofs.RegisterWitness.markedCols sN
          if c == ':' && sP.flowLevel == 0 then
            cPauses := cPauses + 1
            if !(after.all (fun nv => before.contains nv)) then cBad := cBad + 1
            if after.length < before.length then cShrink := cShrink + 1
            if soundB s && monoB s then
              cEligible := cEligible + 1
              if !(coverB sN before) then cBad := cBad + 1
              if !(coverB sN (97 :: before)) then cSuperBad := cSuperBad + 1
              if !before.isEmpty && !(coverB s []) then cEmptyNotCover := cEmptyNotCover + 1
            else cIneligible := cIneligible + 1
          if c == '?' && sP.flowLevel == 0 then
            qPauses := qPauses + 1
            if after.length > before.length then qGrow := qGrow + 1
          s := sN
        | _ => break
      | _ => break
  check state s!"P73 MarkedColsIn.step_value (item 409): block `:` pauses={cPauses} (eligible: Sound ∧ Mono={cEligible}, ineligible={cIneligible}) new mark after `:`={cBad} superset cover broken={cSuperBad} (marks dropped at {cShrink}; `[]` not a cover at {cEmptyNotCover} marked pauses); block `?` pauses={qPauses} mark added={qGrow}"
    (cPauses > 0 && cEligible > 0 && cBad == 0 && cSuperBad == 0 && cEmptyNotCover > 0 && qPauses > 0 && qGrow > 0)

def testOwnMark (state : IO.Ref TestCollector) : IO Unit := do
  -- 74 (item 410) — the `?` park's OWN-MARK fact, read as its contrapositive
  -- `refused_of_markedCols_eq_nil`: at every block-context pause whose pre-state is `Sound`,
  -- `markedCols s = []` → the register is DEAD (`explicitKeyLine = none`) — the markless entry
  -- pack REFUSES, it does not decline.  Buckets: eligible (Sound, flowLevel 0) / ineligible;
  -- markless pauses (the lemma's domain) / live-at-markless (the refutation bucket, must be 0);
  -- negative control: a marked pause has a LIVE register (`Sound.reg`); own-mark presence: the
  -- state after a block `?` dispatch is never markless.
  let mut cEligible := 0
  let mut cIneligible := 0
  let mut cMarkless := 0
  let mut cLiveAtMarkless := 0
  let mut cMarked := 0
  let mut cMarkedLive := 0
  let mut qPauses := 0
  let mut qMarkless := 0
  let corpus : List String :=
    ["a: 1\n", "a: [1, 2]\n", "? a\n: b\n", "- ? a: 1\n  : b\n", "? ? a\n  : b\n: c\n", "? - a\n  - b\n: c\n",
     "a:\n  ? b\n  : c\n", "? [a]: b\n: c\n", "? a\n? b\n: c\n", "k: ? a\n   : b\n", "? &p a: b\n: - w\n",
     "- a: 1\n  b: 2\n", "? a\n:\n  - b\n", "{a: 1}\n", "? {a: 1}\n: 2\n", "- a\n- b\n", "a:\n  - b\n  - c\n",
     "? a\n: b\n? c\n: d\n", "?\n  ? -\n: w\n", "- ? - a\n  : b\n", "k:\n  ? - a\n  : b\n", "? -\n: w\n", "---\n? a\n: b\n...\n"]
  for input in corpus do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          if s.flowLevel == 0 then
            if soundB s then
              cEligible := cEligible + 1
              let marks := L4YAML.Proofs.RegisterWitness.markedCols s
              if marks.isEmpty then
                cMarkless := cMarkless + 1
                if s.explicitKeyLine.isSome then cLiveAtMarkless := cLiveAtMarkless + 1
              else
                cMarked := cMarked + 1
                if s.explicitKeyLine.isSome then cMarkedLive := cMarkedLive + 1
            else cIneligible := cIneligible + 1
          if c == '?' && sP.flowLevel == 0 then
            qPauses := qPauses + 1
            if (L4YAML.Proofs.RegisterWitness.markedCols sN).isEmpty then qMarkless := qMarkless + 1
          s := sN
        | _ => break
      | _ => break
  check state s!"P74 refused_of_markedCols_eq_nil (item 410): block pauses eligible Sound={cEligible} (ineligible={cIneligible}) markless={cMarkless} live register at a markless pause={cLiveAtMarkless} (marked={cMarked}, live there={cMarkedLive}) block `?` pauses={qPauses} markless after={qMarkless}"
    (cEligible > 0 && cMarkless > 0 && cLiveAtMarkless == 0 && cMarked > 0 && cMarkedLive == cMarked && qPauses > 0 && qMarkless == 0)

open L4YAML.Surface in
/-- Priority 75 (item 411), the GRAMMAR half read off the SURFACE CONSTRUCTORS, not the parser:
    every `[187]` entry opens with `?`, with a bare `:` (empty key), or with an implicit key whose
    value is `[192]`'s `s-l+block-node(n, block-out)` or `e-node s-l-comments` — never a compact
    collection, which only `SBlockIndented` ([185]) admits.  By `cases` over the six constructors —
    an anonymous `example` (a Rule 2 reading, not a lemma: it has no consumer and enters no roster). -/
example {n : Nat} {s s' : L4YAML.Surface.SurfPos} (h : L4YAML.Surface.SBlockMapEntry n s s') :
    (∃ s₁, GLit '?' s s₁) ∨ (∃ s₁, GLit ':' s s₁) ∨
    (∃ s₁ s₂, SImplicitKey s s₁ ∧ GLit ':' s₁ s₂ ∧
      (SBlockNode (n + 1) .blockOut s₂ s' ∨ SSLComments s₂ s')) := by
  cases h
  all_goals first
    | exact Or.inl ⟨_, by assumption⟩
    | exact Or.inr (Or.inl ⟨_, by assumption⟩)
    | exact Or.inr (Or.inr ⟨_, _, by assumption, by assumption, Or.inl (by assumption)⟩)
    | exact Or.inr (Or.inr ⟨_, _, by assumption, by assumption, Or.inr (by assumption)⟩)

def testCompactCover (state : IO.Ref TestCollector) : IO Unit := do
  -- 75 (item 411, PRICED) — the compact builder's four cover arms.  The payable witness is
  -- `markedCols sc` with a route per mark; the park's OWN mark rides `h_expl`'s compact route
  -- (`nv = n`), an ANCESTOR's mark needs `h_kslot`'s route, whose premise is the awaited NODE
  -- (`SBlockNode (n + 1) .blockIn`) while the face asks the wider `[185]` slot
  -- (`SBlockIndented n .blockIn`).  Two readings price the gap.  (i) The slot's width is the
  -- GRAMMAR's, not the proof's: an explicit key's value may be a compact collection
  -- (`? - a⏎: b`), an implicit key's may not (`a: - b` — `[192]` is `s-l+block-node` only), so the
  -- implicit-key openers (`colon_open_map_implicit` / `_props`) have no route for the compact
  -- forms — the stage-B obstacle.  The constructor fact is the inversion `example`
  -- above (`cases` over `SBlockMapEntry`); the parser readings here are its executable shadow.  (ii) At every block `?` dispatch the post-state's marks: the
  -- `?`'s own column is the LAST mark (0 misses); own-only parks (a singleton) are the class a
  -- decidable `markedCols sc = [n]` split would pay, nested parks (≥ 2 marks) the class it leaves.
  let accepts (input : String) : Bool := match parseYaml input with | .ok _ => true | .error _ => false
  let implicitCompact : List String :=
    ["a: - b\n", "a: ? b\n   : c\n", "- a: - b\n", "a: &p - b\n", "k:\n  a: - b\n", "a: - b\n   - c\n"]
  let explicitCompact : List String :=
    ["? - a\n: b\n", "? a: 1\n: b\n", "- ? - a\n  : b\n", "? ? a\n  : b\n: c\n", "k:\n  ? - a\n  : b\n", "? - a\n  - b\n: c\n"]
  let implicitNode : List String := ["a:\n  - b\n", "a: b\n", "a:\n  ? b\n  : c\n", "- a:\n    - b\n"]
  let implAcc := (implicitCompact.filter accepts).length
  let explAcc := (explicitCompact.filter accepts).length
  let nodeAcc := (implicitNode.filter accepts).length
  let corpus : List String :=
    ["? a\n: b\n", "- ? a: 1\n  : b\n", "? ? a\n  : b\n: c\n", "? - a\n  - b\n: c\n", "a:\n  ? b\n  : c\n",
     "? [a]: b\n: c\n", "? a\n? b\n: c\n", "k: ? a\n   : b\n", "? &p a: b\n: - w\n", "? a\n:\n  - b\n",
     "? {a: 1}\n: 2\n", "? a\n: b\n? c\n: d\n", "?\n  ? -\n: w\n", "- ? - a\n  : b\n", "k:\n  ? - a\n  : b\n",
     "? -\n: w\n", "---\n? a\n: b\n...\n", "? - ? - a\n  : b\n: c\n", "?\n  ?\n    -\n    - b\n  ? c\n: w\n",
     "?\n  ? [x]: y\n  : z\n: w\n", "? a\n:\n  ? b\n  : c\n"]
  let mut qPauses := 0
  let mut ownLast := 0
  let mut ownOnly := 0
  let mut nested := 0
  let mut markless := 0
  for input in corpus do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          if c == '?' && sP.flowLevel == 0 then
            qPauses := qPauses + 1
            let marks := L4YAML.Proofs.RegisterWitness.markedCols sN
            if marks.getLast? == some sP.col then ownLast := ownLast + 1
            if marks.length == 1 then ownOnly := ownOnly + 1
            else if marks.length ≥ 2 then nested := nested + 1
            else markless := markless + 1
          s := sN
        | _ => break
      | _ => break
  check state s!"P75 compact cover (item 411): implicit-key compact values accepted={implAcc}/{implicitCompact.length} (must be 0) explicit-key compact values accepted={explAcc}/{explicitCompact.length} implicit-key node values accepted={nodeAcc}/{implicitNode.length}; block `?` pauses={qPauses} own mark last={ownLast} own-only={ownOnly} nested={nested} markless={markless}"
    (implAcc == 0 && explAcc == explicitCompact.length && nodeAcc == implicitNode.length &&
     qPauses > 0 && ownLast == qPauses && markless == 0 && ownOnly > 0 && nested > 0)

def testEntryChain (state : IO.Ref TestCollector) : IO Unit := do
  -- 76 (item 412, PAID) — the `?` park's chain ONE FRAME UP over its own entry, carried in
  -- `pendingMapValue.h_expl` and supplied by `question_open_map` from `h_explUp_chainD` through
  -- `h_mcstep` / `hk`: at every block-context `?` dispatch the post-state's projection COVERS the
  -- pre-state's plus the `?`'s own column (every post mark is the own column or a pre mark, and
  -- the own column is a post mark) — the membership case split the supply makes of
  -- `MarkedColsIn sN (k :: nsU)`.  The own column's POSITION is only a reading (it lands at the
  -- tail: `markedCols` walks the indent stack in index order), never asserted.
  -- Negative control: a block `:` dispatch adds no mark.  End to end: the inputs the routed arms
  -- now serve (an ancestor's `:` after an inner `?` key, compact or not) parse, and so does the
  -- one input class the `NotQuestionPark` arms still decline (the explicit `:` park's compact
  -- value under an outer `?`) — a decline is not a refusal.
  let accepts (input : String) : Bool := match parseYaml input with | .ok _ => true | .error _ => false
  let routed : List String :=
    ["? ? a\n  : b\n: c\n", "? - ? a\n    : b\n: c\n", "? ? - a\n  : b\n: c\n", "?\n  ? a: 1\n  : b\n: c\n",
     "? ? a\n: c\n", "k:\n  ? ? a\n    : b\n  : c\n"]
  let declined : List String := ["? ? a\n  : - b\n: c\n", "? ? a\n  : b: 1\n: c\n"]
  let routedAcc := (routed.filter accepts).length
  let declinedAcc := (declined.filter accepts).length
  let corpus : List String :=
    ["? a\n: b\n", "? ? a\n  : b\n: c\n", "- ? a: 1\n  : b\n", "? - a\n  - b\n: c\n", "a:\n  ? b\n  : c\n",
     "? a\n? b\n: c\n", "k: ? a\n   : b\n", "? &p a: b\n: - w\n", "?\n  ? -\n: w\n", "- ? - a\n  : b\n",
     "k:\n  ? - a\n  : b\n", "? -\n: w\n", "? - ? - a\n  : b\n: c\n", "?\n  ?\n    -\n    - b\n  ? c\n: w\n",
     "? a\n:\n  ? b\n  : c\n", "? ? ? a\n    : b\n  : c\n: d\n"]
  let mut qPauses := 0
  let mut coverOK := 0
  let mut ownAtTail := 0
  let mut ownAtHead := 0
  let mut colonPauses := 0
  let mut colonAdds := 0
  for input in corpus do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          if sP.flowLevel == 0 then
            let before := L4YAML.Proofs.RegisterWitness.markedCols sP
            let after := L4YAML.Proofs.RegisterWitness.markedCols sN
            if c == '?' then
              qPauses := qPauses + 1
              -- What the supply uses is the COVER (`h_mcstep`: `MarkedColsIn s' (k :: nsU)`, read by
              -- membership): every post mark is the own column or a pre mark, and the own column is a
              -- post mark.  WHERE the own column sits is a reading, not the invariant — `markedCols`
              -- walks the indent stack in index order, so a push lands at the TAIL.
              if after.all (fun m => m == sP.col || before.contains m) && after.contains sP.col then
                coverOK := coverOK + 1
              if after == before ++ [sP.col] then ownAtTail := ownAtTail + 1
              if after == sP.col :: before then ownAtHead := ownAtHead + 1
            else if c == ':' then
              colonPauses := colonPauses + 1
              if after.length > before.length then colonAdds := colonAdds + 1
          s := sN
        | _ => break
      | _ => break
  check state s!"P76 entry chain (item 412): block `?` pauses={qPauses} post marks ⊆ own column ∪ pre marks with own ∈ post (the cover `h_mcstep` supplies)={coverOK} — own column at tail={ownAtTail} at head={ownAtHead} (order is a reading, not the invariant); block `:` pauses={colonPauses} adding a mark={colonAdds} (must be 0); routed inputs accepted={routedAcc}/{routed.length} declined-class inputs accepted={declinedAcc}/{declined.length}"
    (qPauses > 0 && coverOK == qPauses && colonPauses > 0 && colonAdds == 0 &&
     routedAcc == routed.length && declinedAcc == declined.length)

-- 77, grammar half (item 413) — the surface ROUTE `h_chainUp` carries, challenged off the
-- constructors (a refutation is a build failure).  `compact_open_map` states the chain over the
-- `-` / slot park's CONTENT `SBlockIndented n ctx`, not over its own entry: these examples pin
-- (a) the wrapper the supply builds — a lone compact `?` entry IS that content through
-- `SCompactMapTail.nil`; (b) the discharge — an ancestor `:` at a marked column `nv` after that
-- content resumes `[map nv]` under the route both callers hold; (c) the `-` park's relay — its
-- `h_kslotUp` (content in `.blockIn` + a compact-sequence tail) reaches the same route at the `nil`
-- tail; (d) the refutation bucket — a compact-map tail that MOVES has a sibling entry, which the
-- lone-entry wrapper never builds (`cases` over `SCompactMapTail`'s two constructors).
section CompactChainGrammar
open L4YAML.Surface L4YAML.Proofs.IndentStackCover L4YAML.Proofs.StreamAccum

example (n m : Nat) (ctx : YamlContext) (sp_e sp_i sp_v : SurfPos)
    (h_ind : SIndent m sp_e sp_i) (h_entry : SBlockMapEntry (n + 1 + m) sp_i sp_v) :
    SBlockIndented n ctx sp_e sp_v :=
  SBlockIndented.compactMap n ctx m sp_e sp_i sp_v h_ind
    (SCompactMap.mk (n + 1 + m) sp_i sp_v sp_v h_entry (SCompactMapTail.nil (n + 1 + m) sp_v))

example (n m nv : Nat) (ctx : YamlContext) (sp_start sp_e sp_i sp_v sp_c sp_c' sp_w : SurfPos)
    (h_ind : SIndent m sp_e sp_i) (h_entry : SBlockMapEntry (n + 1 + m) sp_i sp_v)
    (h_ci : SIndent nv sp_v sp_c) (h_colon : GLit ':' sp_c sp_c')
    (h_val : SBlockIndented nv .blockOut sp_c' sp_w)
    (route : ∀ sp_m : SurfPos, SBlockIndented n ctx sp_e sp_m →
      ∀ sp_i sp_c : SurfPos, SIndent nv sp_m sp_i → GLit ':' sp_i sp_c →
      ∀ sp_v : SurfPos, SBlockIndented nv .blockOut sp_c sp_v →
      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v) :
    ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_w :=
  route sp_v
    (SBlockIndented.compactMap n ctx m sp_e sp_i sp_v h_ind
      (SCompactMap.mk (n + 1 + m) sp_i sp_v sp_v h_entry (SCompactMapTail.nil (n + 1 + m) sp_v)))
    sp_c sp_c' h_ci h_colon sp_w h_val

example (n nv : Nat) (sp_start sp_scan : SurfPos)
    (h_kslotUp : ∀ sp_m : SurfPos, SBlockIndented n .blockIn sp_scan sp_m →
      ∀ sp_e : SurfPos, SCompactSeqTail n sp_m sp_e →
      ∀ sp_i sp_c : SurfPos, SIndent nv sp_e sp_i → GLit ':' sp_i sp_c →
      ∀ sp_v : SurfPos, SBlockIndented nv .blockOut sp_c sp_v →
      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v) :
    ∀ sp_m : SurfPos, SBlockIndented n .blockIn sp_scan sp_m →
      ∀ sp_i sp_c : SurfPos, SIndent nv sp_m sp_i → GLit ':' sp_i sp_c →
      ∀ sp_v : SurfPos, SBlockIndented nv .blockOut sp_c sp_v →
      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v :=
  fun sp_m h_m => h_kslotUp sp_m h_m sp_m (SCompactSeqTail.nil n sp_m)

example (k : Nat) (s s' : SurfPos) (h : SCompactMapTail k s s') (hne : s ≠ s') :
    ∃ s₁ s₂ : SurfPos, SIndent k s s₁ ∧ SBlockMapEntry k s₁ s₂ := by
  cases h with
  | nil => exact absurd rfl hne
  | cons _ _ s₁ s₂ _ h_ind h_entry _ => exact ⟨s₁, s₂, h_ind, h_entry⟩

end CompactChainGrammar

def testCompactChain (state : IO.Ref TestCollector) : IO Unit := do
  -- 77 (item 413, PAID) — `compact_open_map`'s chain ONE FRAME UP, supplied from the `-` / slot
  -- park's chain over the entry's CONTENT (`h_chainUp`, on the PRE-state's projection) through the
  -- compact `?`'s own mark step (`h_mcstep`).  What the supply reads at every COMPACT `?` dispatch
  -- (a `?` on the line of the `-` / `?` / `:` that parked the pending): (i) the cover — every post
  -- mark is the own column or a pre mark, and the own column is a post mark (so a post mark OTHER
  -- than the own column is a pre mark: the `nv ≠ n + 1 + m` case hands `up` a member of
  -- `markedCols sc`); (ii) the own column read off the pre-state (`hk`) IS the `?`'s surface column.
  -- Hypothesis buckets: compact pauses whose pre-state holds a mark (the chain's domain is
  -- non-empty — the informative case) vs markless (the chain is vacuous there).  Refutation
  -- bucket: a compact `-` dispatch adds no mark (its chain rides the UNCHANGED domain,
  -- `h_mcstep_ne`).  End to end: inputs whose ancestor `:` lands after a compact `?` entry parse.
  let accepts (input : String) : Bool := match parseYaml input with | .ok _ => true | .error _ => false
  let routed : List String :=
    ["? - ? a\n    : b\n: c\n", "- ? a\n  : b\n", "? ? ? a\n    : b\n  : c\n: d\n", "? a\n: ? b\n  : c\n",
     "- - ? a\n    : b\n", "?\n  - ? a\n    : b\n: c\n", "? - ? a\n: c\n", "- ? ? a\n    : b\n  : c\n"]
  let routedAcc := (routed.filter accepts).length
  let corpus : List String := routed ++
    ["? a\n: b\n", "? ? a\n  : b\n: c\n", "- ? a: 1\n  : b\n", "? - a\n  - b\n: c\n", "a:\n  ? b\n  : c\n",
     "? a\n? b\n: c\n", "? &p a: b\n: - w\n", "?\n  ? -\n: w\n", "- ? - a\n  : b\n",
     "k:\n  ? - a\n  : b\n", "? -\n: w\n", "? - ? - a\n  : b\n: c\n", "?\n  ?\n    -\n    - b\n  ? c\n: w\n",
     "? a\n:\n  ? b\n  : c\n", "? ? ? a\n    : b\n  : c\n: d\n", "- - ? - a\n      : b\n"]
  -- A COMPACT pause: the indicator stands on the line of a `-` / `?` / `:` with only spaces between.
  let compactAt (input : String) (sP : L4YAML.Scanner.ScannerState) : Bool :=
    match ((input.toList.take sP.offset).reverse.dropWhile (· == ' ')) with
    | ch :: _ => ch == '-' || ch == '?' || ch == ':'
    | [] => false
  let surfCol (input : String) (sP : L4YAML.Scanner.ScannerState) : Nat :=
    ((input.toList.take sP.offset).reverse.takeWhile (· != '\n')).length
  let mut cPauses := 0
  let mut preMarked := 0
  let mut preMarkless := 0
  let mut coverOK := 0
  let mut colOK := 0
  let mut dashPauses := 0
  let mut dashAdds := 0
  for input in corpus do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          if sP.flowLevel == 0 && compactAt input sP then
            let before := L4YAML.Proofs.RegisterWitness.markedCols sP
            let after := L4YAML.Proofs.RegisterWitness.markedCols sN
            if c == '?' then
              cPauses := cPauses + 1
              if before.isEmpty then preMarkless := preMarkless + 1 else preMarked := preMarked + 1
              if after.all (fun x => x == sP.col || before.contains x) && after.contains sP.col then
                coverOK := coverOK + 1
              if surfCol input sP == sP.col then colOK := colOK + 1
            else if c == '-' then
              dashPauses := dashPauses + 1
              if after.length > before.length then dashAdds := dashAdds + 1
          s := sN
        | _ => break
      | _ => break
  check state s!"P77 compact chain (item 413): compact `?` pauses={cPauses} (pre-state marked={preMarked} markless={preMarkless}) cover (own ∈ post, post ⊆ own ∪ pre — what `h_mcstep` hands the supply)={coverOK} own column = the `?`'s surface column (`hk`)={colOK}; compact `-` pauses={dashPauses} adding a mark={dashAdds} (must be 0); routed inputs accepted={routedAcc}/{routed.length}"
    (cPauses > 0 && preMarked > 0 && preMarkless > 0 && coverOK == cPauses && colOK == cPauses &&
     dashPauses > 0 && dashAdds == 0 && routedAcc == routed.length)

def testRefusedAtParks (state : IO.Ref TestCollector) : IO Unit := do
  -- 78 (item 414, PRICED) — `PackAlt sc := ExplicitValueRefused sc` (`sc.explicitKeyLine = none`)
  -- read at every park the residue's 85 declines stand on.  Hypothesis bucket: a `?` dispatch
  -- ARMS the register (`scanKeyIx` writes `explicitKeyLine := some line`, block and flow alike), so
  -- the refusal is FALSE at every post-`?` state — the `?`-park fields (`h_kslot`, `h_kslotUp`,
  -- `h_explUp_chain*`, the openers' chains) can never pay it; a `:` at the register's line clears
  -- it (`scanValue`) UNLESS an enclosing `?` is pending — then the `:` re-arms the register from
  -- the innermost pending key (`readPendingKey`); a `-` / content step carries it; a flow OPEN
  -- clears it for the interior and saves it on `explicitKeyStack`, the close restores it — so the
  -- register alone is dead inside `? [1, 2]` while the `?` is pending (the flow frame's `PackAltG`).  Refutation bucket for the pay as stated:
  -- a dead register at a non-`?` park (`-` entry, implicit key) — where `PackAlt.ofRefused` IS
  -- available — must be the ONLY state kind the predicate holds at.
  let corpus : List String :=
    ["? a\n: b\n", "? ? a\n  : b\n: c\n", "- ? a: 1\n  : b\n", "? - a\n  - b\n: c\n", "a:\n  ? b\n  : c\n",
     "? a\n? b\n: c\n", "k: ? a\n   : b\n", "?\n  ? -\n: w\n", "- ? - a\n  : b\n", "k:\n  ? - a\n  : b\n",
     "? -\n: w\n", "? - ? - a\n  : b\n: c\n", "? ? ? a\n    : b\n  : c\n: d\n", "- a\n- b\n", "a: 1\nb: 2\n",
     "- - a\n  - b\n", "k:\n  - a\n  - b\n", "[? a : b]\n", "{? a : b}\n", "- ? a\n  : b\n- c\n",
     "? [1, 2]\n: - w\n", "? {a: b}\n: c\n", "? [a: b]\n: v\n", "- ? [x]\n  : y\n", "? ? [1]\n  : b\n: c\n"]
  let mut qPauses := 0
  let mut qArmedAfter := 0
  let mut colonPauses := 0
  let mut colonClears := 0
  let mut colonRestores := 0
  let mut colonArmedBefore := 0
  let mut dashPauses := 0
  let mut dashCarries := 0
  let mut deadParks := 0
  let mut armedParks := 0
  let mut flowOpensArmed := 0
  let mut flowOpensSaved := 0
  let mut flowClosesSaved := 0
  let mut flowClosesRestored := 0
  for input in corpus do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          if c == '?' then
            qPauses := qPauses + 1
            if sN.explicitKeyLine.isSome then qArmedAfter := qArmedAfter + 1
          else if c == ':' && sP.flowLevel == 0 then
            colonPauses := colonPauses + 1
            if sP.explicitKeyLine.isSome then colonArmedBefore := colonArmedBefore + 1
            if sP.explicitKeyLine.isSome && sN.explicitKeyLine.isNone then colonClears := colonClears + 1
            if sP.explicitKeyLine.isSome && sN.explicitKeyLine.isSome &&
                sN.pendingKeys.toList.contains sN.explicitKeyLine then colonRestores := colonRestores + 1
          else if c == '-' && sP.flowLevel == 0 then
            dashPauses := dashPauses + 1
            if sN.explicitKeyLine == sP.explicitKeyLine then dashCarries := dashCarries + 1
          if (c == '[' || c == '{') && sP.explicitKeyLine.isSome then
            flowOpensArmed := flowOpensArmed + 1
            if sN.explicitKeyLine.isNone && sN.explicitKeyStack.back? == some (sP.explicitKeyLine, sP.explicitKeyCol) then
              flowOpensSaved := flowOpensSaved + 1
          if (c == ']' || c == '}') then
            match sP.explicitKeyStack.back? with
            | some (some l, col) =>
              flowClosesSaved := flowClosesSaved + 1
              if sN.explicitKeyLine == some l && sN.explicitKeyCol == col then flowClosesRestored := flowClosesRestored + 1
            | _ => pure ()
          if sP.flowLevel == 0 then
            if sP.explicitKeyLine.isNone then deadParks := deadParks + 1 else armedParks := armedParks + 1
          s := sN
        | _ => break
      | _ => break
  check state s!"P78 refusal at parks (item 414): `?` pauses={qPauses} register ARMED after=({qArmedAfter} — must be all: `ExplicitValueRefused` is FALSE at every `?` park, the ns-class residue cannot pay it); block `:` pauses={colonPauses} armed before={colonArmedBefore} cleared by the `:`={colonClears} RE-ARMED from an enclosing `?` (`readPendingKey`)={colonRestores} (cleared + re-armed must equal armed-before — the naive `a `:` clears` was REFUTED by the nested-`?` inputs); block `-` pauses={dashPauses} carrying the register unchanged={dashCarries} (must be all); block pauses standing on a DEAD register={deadParks} on an ARMED one={armedParks}; flow opens under an armed register={flowOpensArmed} clearing it and SAVING the pair on `explicitKeyStack`={flowOpensSaved} (must be all: the interior reads a dead register while the `?` is still pending — `explicitKeyLine = none` alone is NOT `no ? pending`), flow closes with a saved `?`={flowClosesSaved} RESTORING it={flowClosesRestored} (must be all)"
    (qPauses > 0 && qArmedAfter == qPauses && colonPauses > 0 && colonClears + colonRestores == colonArmedBefore &&
     dashPauses > 0 && dashCarries == dashPauses && deadParks > 0 && armedParks > 0 &&
     flowOpensArmed > 0 && flowOpensSaved == flowOpensArmed && flowClosesSaved > 0 && flowClosesRestored == flowClosesSaved)

-- 79, grammar half (item 415) — the surface ROUTE `explEntryChain_of_keyContent` carries,
-- challenged off the constructors (a refutation is a build failure).  The lemma reads the `?`
-- entry's chain at its KEY content and decides by column: (a) at the entry's OWN column the `:`
-- line IS the explicit value — the entry is `[186] explicit` and `route` alone (item 412's entry
-- route, no `up`) closes the stream at the nil tail, one resume level; (b) at any OTHER marked
-- column the entry is KEY-ONLY (`explicitEmpty`) and `up` (item 413's chain one frame up) resumes
-- that column; (c) the lemma's discharge under both hypotheses at a marked column; (d) the
-- refutation bucket — the empty entry ends where the KEY ends (`sp_m`), the explicit one where the
-- VALUE ends (`sp_v`): routing the own column through `explicitEmpty` proves the resume at `sp_m`,
-- which is NOT the owed position `sp_v` once the value is non-empty, so the own-column arm cannot
-- be served by the empty entry (the review's "accidental empty entry" is a type error, not a
-- silently green route).
section InlDeclinesGrammar
open L4YAML.Surface L4YAML.Proofs.IndentStackCover L4YAML.Proofs.RegisterWitness L4YAML.Proofs.StreamAccum

example (n : Nat) (sp_start sp_q sp_scan sp_m sp_i sp_c sp_v : SurfPos)
    (h_qlit : GLit '?' sp_q sp_scan) (h_key : SBlockIndented n .blockOut sp_scan sp_m)
    (h_ind : SIndent n sp_m sp_i) (h_lit : GLit ':' sp_i sp_c)
    (h_val : SBlockIndented n .blockOut sp_c sp_v)
    (route : ∀ sp_v : SurfPos, SBlockMapEntry n sp_q sp_v →
      ∀ sp_e : SurfPos, SCompactMapTail n sp_v sp_e → SLYamlStream sp_start sp_e) :
    ResumeFrames (SLYamlStream sp_start) [FrameLevel.map n] sp_v :=
  ResumeFrames.one
    (route sp_v (SBlockMapEntry.explicit n sp_q sp_scan sp_m sp_i sp_c sp_v h_qlit h_key h_ind h_lit h_val))

example (n nv : Nat) (sc : L4YAML.Scanner.ScannerState) (sp_start sp_q sp_scan sp_m sp_i sp_c sp_v : SurfPos)
    (hmem : nv ∈ markedCols sc) (hne : nv ≠ n)
    (h_qlit : GLit '?' sp_q sp_scan) (h_key : SBlockIndented n .blockOut sp_scan sp_m)
    (h_ind : SIndent nv sp_m sp_i) (h_lit : GLit ':' sp_i sp_c)
    (h_val : SBlockIndented nv .blockOut sp_c sp_v)
    (up : ∀ nv ∈ markedCols sc, nv ≠ n →
      ∀ sp_v : SurfPos, SBlockMapEntry n sp_q sp_v →
      ∀ sp_i sp_c : SurfPos, SIndent nv sp_v sp_i → GLit ':' sp_i sp_c →
      ∀ sp_w : SurfPos, SBlockIndented nv .blockOut sp_c sp_w →
      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_w) :
    ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v :=
  up nv hmem hne sp_m (SBlockMapEntry.explicitEmpty n sp_q sp_scan sp_m h_qlit h_key)
    sp_i sp_c h_ind h_lit sp_v h_val

example (n nv : Nat) (sc : L4YAML.Scanner.ScannerState) (sp_start sp_q sp_scan sp_m sp_i sp_c sp_v : SurfPos)
    (hmem : nv ∈ markedCols sc)
    (h_qlit : GLit '?' sp_q sp_scan) (h_key : SBlockIndented n .blockOut sp_scan sp_m)
    (h_ind : SIndent nv sp_m sp_i) (h_lit : GLit ':' sp_i sp_c)
    (h_val : SBlockIndented nv .blockOut sp_c sp_v)
    (route : ∀ sp_v : SurfPos, SBlockMapEntry n sp_q sp_v →
      ∀ sp_e : SurfPos, SCompactMapTail n sp_v sp_e → SLYamlStream sp_start sp_e)
    (up : ∀ nv ∈ markedCols sc, nv ≠ n →
      ∀ sp_v : SurfPos, SBlockMapEntry n sp_q sp_v →
      ∀ sp_i sp_c : SurfPos, SIndent nv sp_v sp_i → GLit ':' sp_i sp_c →
      ∀ sp_w : SurfPos, SBlockIndented nv .blockOut sp_c sp_w →
      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_w) :
    ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v :=
  explEntryChain_of_keyContent h_qlit route up nv hmem sp_m h_key sp_i sp_c h_ind h_lit sp_v h_val

example (n : Nat) (sp_start sp_q sp_scan sp_m : SurfPos)
    (h_qlit : GLit '?' sp_q sp_scan) (h_key : SBlockIndented n .blockOut sp_scan sp_m)
    (route : ∀ sp_v : SurfPos, SBlockMapEntry n sp_q sp_v →
      ∀ sp_e : SurfPos, SCompactMapTail n sp_v sp_e → SLYamlStream sp_start sp_e) :
    ResumeFrames (SLYamlStream sp_start) [FrameLevel.map n] sp_m :=
  ResumeFrames.one (route sp_m (SBlockMapEntry.explicitEmpty n sp_q sp_scan sp_m h_qlit h_key))

end InlDeclinesGrammar

def testInlDeclinesPaid (state : IO.Ref TestCollector) : IO Unit := do
  -- 79 (item 415, PAID 7 of 14) — the statement-shaped `Or.inl … => Or.inr trivial` declines whose
  -- upstream route now reaches the site: the `?` entry's chain read at its KEY content
  -- (`explEntryChain_of_keyContent`: a `:` at the entry's OWN column completes `[186] explicit`
  -- and closes the stream — one resume level; a `:` at an ENCLOSING mark leaves a key-only entry
  -- (`explicitEmpty`) and item 412's chain one frame up resumes that column), the props run's
  -- node as the entry's content at a nil tail, the compact fill's ancestor list, and the
  -- relay of an upstream decline.  Hypothesis buckets on the parser: at every block `:` pause
  -- standing on an ARMED register, the `:` lands at the register's own column (the entry
  -- completes) or RIGHT of it only on the register's OWN LINE (an implicit key inside the `?`'s
  -- key content, `? a: [1]` — `[186]`'s key node, not a value line); no `:` lands right of the
  -- register on a LATER line, and LEFT of it is a READING, not a claim: a `:` at an ENCLOSING
  -- `?`'s column (`? ? a\n: c`, the key-only inner entry the `nv ≠ n` arm serves) pauses with
  -- the register already reading that enclosing `?` — the scanner presents the proof's
  -- `explicitEmpty` inputs as own-column pauses of the outer register.  The first cut claimed
  -- "nothing right of it" and "left of it must occur"; the same-line implicit keys refuted the
  -- first (4 of 33) and the restored register the second (0 of 33), and the buckets were restated.
  -- End to end: the routed inputs parse.  The seven UNPAID (`accum_content_pending` ×6: the
  -- props park's slot `h_kslotE` carries a bare `∃ nv` with no domain; `colon_open_map`: a
  -- frames fact where a marked-column chain is owed) are a class the item names, not refutes:
  -- their inputs parse too (`declinedClass`).
  let accepts (input : String) : Bool := match parseYaml input with | .ok _ => true | .error _ => false
  let routed : List String :=
    ["k:\n  ? a\n  : b\n", "k:\n  ? ? a\n    : b\n  : c\n", "? ? a\n  : b\n: c\n", "? a\n: b\n",
     "? [1]: b\n: - w\n", "? ? [1]\n  : b\n: w\n", "? [1]\n: v\n", "? a: [1]\n: - w\n",
     "? - &a x\n: - w\n", "? - !!str x\n: w\n", "? - a\n: - w\n", "? - ? - a\n    : b\n: c\n",
     "? ? - a\n  : b\n: c\n", "k:\n  ? a: |\n      x\n  : d\n", "? a: \"p\n    q\"\n: - w\n",
     "? ? a\n: c\n", "k:\n  ? ? a\n  : c\n", "- ? ? a\n  : c\n", "? ? - a\n: c\n"]
  let declinedClass : List String := ["? &a x\n: w\n", "? !!str x\n: w\n", "- ? &a x\n  : w\n", "? a\n:\n  ? b\n  : c\n"]
  let routedAcc := (routed.filter accepts).length
  let declinedAcc := (declinedClass.filter accepts).length
  let mut armedColons := 0
  let mut ownCol := 0
  let mut leftOfOwn := 0
  let mut rightInKey := 0
  let mut rightOfOwn := 0
  for input in routed ++ declinedClass do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          if c == ':' && sP.flowLevel == 0 && sP.explicitKeyLine.isSome then
            armedColons := armedColons + 1
            if (sP.col : Int) == sP.explicitKeyCol then ownCol := ownCol + 1
            else if (sP.col : Int) < sP.explicitKeyCol then leftOfOwn := leftOfOwn + 1
            else if sP.explicitKeyLine == some sP.line then rightInKey := rightInKey + 1
            else rightOfOwn := rightOfOwn + 1
          s := sN
        | _ => break
      | _ => break
  check state s!"P79 Or.inl declines paid (item 415): block `:` pauses on an ARMED register={armedColons} — at the register's own column (the `?` entry completes, `explicit`)={ownCol} left of it (a reading: an enclosing `?`'s `:` pauses on the register already restored to that `?`)={leftOfOwn} right of it on the `?`'s own line (an implicit key inside the key content — must occur)={rightInKey} right of it on a later line={rightOfOwn} (must be 0); routed inputs accepted={routedAcc}/{routed.length}; declined-class inputs accepted={declinedAcc}/{declinedClass.length}"
    (armedColons > 0 && ownCol > 0 && rightInKey > 0 && rightOfOwn == 0 &&
     routedAcc == routed.length && declinedAcc == declinedClass.length)

def testKslotEDomain (state : IO.Ref TestCollector) : IO Unit := do
  -- 80 (item 416, PAID) — `pendingProps.h_kslotE` DOMAINED over the park's projection
  -- (`∀ nv ∈ markedCols sc` in place of a bare `∃ nv`): the three informative producers hand
  -- their chain on through `markedCols_mem_of_step_content` (a content dispatch adds no mark),
  -- and the six `accum_content_pending` sites item 415 stopped at take the route.  What the
  -- transport reads, at every CONTENT pause (the token is neither an indicator `? : - [ ] { }`
  -- nor a break) on the parser: the post-state's marked columns are EXACTLY the pre-state's —
  -- no mark added, none removed (the lemma needs ⊆; equality is the stronger reading and is
  -- reported).  Negative control: a `?` pause adds its own column.  End to end: the props-park
  -- inputs item 415 named as its stopped class (`? &a x\n: w`, …) parse, with nested, compact
  -- and mapping-valued forms of the decorated explicit key.
  let accepts (input : String) : Bool := match parseYaml input with | .ok _ => true | .error _ => false
  let routed : List String :=
    ["? &a x\n: w\n", "? !!str x\n: w\n", "- ? &a x\n  : w\n", "? ? &a x\n  : w\n: v\n",
     "k:\n  ? &a x\n  : w\n", "? - &a x\n: w\n", "? &a\n  b: 1\n: w\n", "? !!map\n  b: 1\n: w\n",
     "? &a !!str x\n: w\n", "? &a [1]\n: w\n", "? &a x\n:\n  ? &b y\n  : z\n", "? &a x # c\n: w\n"]
  let routedAcc := (routed.filter accepts).length
  -- The lemma's span is the WHOLE step `sc → s'` (preprocess + content dispatch), so the gate
  -- compares the pre-state `s` the step was taken from with `sN`; the two halves (`s → sP`,
  -- `sP → sN`) are reported separately as readings.  A pause is ELIGIBLE when the lemma's
  -- hypotheses hold (preprocess pauses at block level on a character that is neither an
  -- indicator nor a break); the ineligible pauses are counted, not asserted on.
  let mut contentPauses := 0
  let mut ineligible := 0
  let mut sameMarks := 0
  let mut shrank := 0
  let mut grew := 0
  let mut prepSame := 0
  let mut dispSame := 0
  let mut qPauses := 0
  let mut qAdded := 0
  for input in routed do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          let pre := markedColsOf s.pendingKeys s.indentColumns
          let mid := markedColsOf sP.pendingKeys sP.indentColumns
          let after := markedColsOf sN.pendingKeys sN.indentColumns
          if sP.flowLevel == 0 && !"?:-[]{}\n".toList.contains c then
            contentPauses := contentPauses + 1
            if after == pre then sameMarks := sameMarks + 1
            else if after.all (· ∈ pre) then shrank := shrank + 1
            else grew := grew + 1
            if mid == pre then prepSame := prepSame + 1
            if after == mid then dispSame := dispSame + 1
          else
            ineligible := ineligible + 1
          if sP.flowLevel == 0 && c == '?' then
            qPauses := qPauses + 1
            if sP.col ∈ after && !(sP.col ∈ mid) then qAdded := qAdded + 1
          s := sN
        | _ => break
      | _ => break
  check state s!"P80 h_kslotE domained (item 416): eligible block content steps={contentPauses} (ineligible pauses={ineligible}) — over the lemma's span s → s': marks unchanged={sameMarks} shrank (still ⊆)={shrank} grew={grew} (must be 0: the step adds no mark); halves: preprocess s → sP unchanged={prepSame}, dispatch sP → s' unchanged={dispSame}; `?` pauses={qPauses} adding their own column={qAdded} (negative control, must be all); props-park inputs accepted={routedAcc}/{routed.length}"
    (contentPauses > 0 && grew == 0 && qPauses > 0 && qAdded == qPauses && routedAcc == routed.length)

-- 81, grammar half (item 417) — `colon_open_map`'s `h_kslot` PAID from the caller's chain one
-- frame up (item 412's `h_explUp_chainD`, stated over ENTRIES at `k`): the `:` arm builds the
-- `[189]` entry from the awaited node (`SBlockMapEntry.emptyKeyNode`), so the owed NODE chain is
-- the held ENTRY chain at that entry; the domain crosses the `:` by the mark step.  Each example
-- is one obligation the pay discharges, read off the surface constructors.
section ColonChainGrammar
open L4YAML.Surface L4YAML.Proofs.IndentStackCover L4YAML.Proofs.RegisterWitness L4YAML.Proofs.StreamAccum

-- (i) the node → the `[189]` entry: `emptyKeyNode` wants the node at `k + 1` in `.blockOut`;
-- the slot's node is `.blockIn`, converted by `SBlockNode_blockIn_to_blockOut`.
example (k : Nat) (sp_ind sp_scan' sp_m : SurfPos)
    (h_lit : GLit ':' sp_ind sp_scan') (h_node : SBlockNode (k + 1) .blockIn sp_scan' sp_m) :
    SBlockMapEntry k sp_ind sp_m :=
  SBlockMapEntry.emptyKeyNode k sp_ind sp_scan' sp_m h_lit (L4YAML.Proofs.NodeProduction.SBlockNode_blockIn_to_blockOut h_node)

-- (ii) the pay's term: the entry chain at that entry IS the slot chain, for every marked column.
example (k nv : Nat) (sc : L4YAML.Scanner.ScannerState) (ns : List Nat)
    (sp_start sp_ind sp_scan' sp_m sp_i sp_c sp_v : SurfPos)
    (hmem : nv ∈ ns) (h_lit : GLit ':' sp_ind sp_scan')
    (h_node : SBlockNode (k + 1) .blockIn sp_scan' sp_m)
    (h_ind : SIndent nv sp_m sp_i) (h_colon : GLit ':' sp_i sp_c)
    (h_val : SBlockIndented nv .blockOut sp_c sp_v)
    (chain : ∀ nv ∈ ns, ∀ sp_v : SurfPos, SBlockMapEntry k sp_ind sp_v →
      ∀ sp_i sp_c : SurfPos, SIndent nv sp_v sp_i → GLit ':' sp_i sp_c →
      ∀ sp_w : SurfPos, SBlockIndented nv .blockOut sp_c sp_w →
      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_w) :
    ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v :=
  chain nv hmem sp_m
    (SBlockMapEntry.emptyKeyNode k sp_ind sp_scan' sp_m h_lit (L4YAML.Proofs.NodeProduction.SBlockNode_blockIn_to_blockOut h_node))
    sp_i sp_c h_ind h_colon sp_v h_val

-- (iii) the domain crosses the `:`: a non-`?` indicator adds no mark (`h_mcstep_ne`), so the
-- pre-state's `MarkedColsIn` is the post-state's — the `∃ ns` the new park's `h_kslot` carries.
example (sc s' : L4YAML.Scanner.ScannerState) (ns : List Nat) (hdom : MarkedColsIn sc ns)
    (h_mcstep_ne : ':' ≠ '?' → ∀ ns : List Nat, MarkedColsIn sc ns → MarkedColsIn s' ns) :
    MarkedColsIn s' ns :=
  h_mcstep_ne (by decide) ns hdom

-- Refutation bucket: the OTHER `[189]` constructor, `emptyKeyEmpty`, closes the entry on
-- comments (`SSLComments sp_scan' sp_m`) — the slot's hypothesis is a NODE, which is no
-- comments run, so the node arm cannot be paid through it; the entry it builds ends at the
-- comments' end, where no awaited node stands.  Stated as the obligation the wrong arm would owe.
example (k : Nat) (sp_ind sp_scan' sp_m : SurfPos)
    (h_lit : GLit ':' sp_ind sp_scan') (h_ssl : SSLComments sp_scan' sp_m) :
    SBlockMapEntry k sp_ind sp_m :=
  SBlockMapEntry.emptyKeyEmpty k sp_ind sp_scan' sp_m h_lit h_ssl
end ColonChainGrammar

/-- Priority 81's root renderer: the WHOLE composed value, nested (`{k: v, …}` / `[a, …]`, an
empty scalar as `~`, an alias as `*x`; styles, tags and anchors dropped), so a nested `:` entry
that vanished or landed as a sibling changes the string. -/
partial def p81Shape : YamlValue → String
  | .scalar s => if s.content.isEmpty then "~" else s.content
  | .sequence _ items .. => "[" ++ ", ".intercalate (items.toList.map p81Shape) ++ "]"
  | .mapping _ pairs .. => "{" ++ ", ".intercalate (pairs.toList.map (fun (k, v) => p81Shape k ++ ": " ++ p81Shape v)) ++ "}"
  | .alias n => "*" ++ n

def testColonChainRelay (state : IO.Ref TestCollector) : IO Unit := do
  -- 81 (item 417, PAID) — the scanner half of the relay: the mark step `h_mcstep_ne` the pay
  -- carries the domain across says a `:` dispatch adds no mark — over the WHOLE step `s → s'`
  -- (preprocess + block-indicator dispatch), on the ELIGIBLE steps (the preprocess pauses on a
  -- block-level `:`).  The lemma needs ⊆; whether a `:` also REMOVES a mark (the explicit key it
  -- answers) is reported as a reading, not asserted.  Negative control: a `?` adds its own column.
  -- End to end: the `:`-landing inputs of item 415's stopped class G (a `:` at a dedent / line
  -- start opening a mapping under open `?` frames — item 197's `?⏎  ?⏎    - a⏎  : b⏎  : c⏎: w`).
  -- Each landing is paired with the WHOLE value it must compose to (`p81Shape`, one document), so a
  -- `:` read as a sibling, a dropped nested entry or a refusal fails its row; every row must hold
  -- (no threshold).
  let rootShape (input : String) : String := match parseYaml input with
    | .ok docs =>
      if docs.size != 1 then s!"docs {docs.size}" else (docs[0]?.map (fun d => p81Shape d.value)).getD "no doc"
    | .error _ => "refused"
  let landings : List (String × String) :=
    [("?\n  ?\n    - a\n  : b\n  : c\n: w\n", "{{[a]: b, ~: c}: w}"), (": v\n", "{~: v}"), (": v\n: w\n", "{~: v, ~: w}"),
     ("? a\n: b\n: c\n", "{a: b, ~: c}"), ("k:\n  : v\n", "{k: {~: v}}"), ("- : v\n", "[{~: v}]"),
     ("?\n  - a\n: b\n: c\n", "{[a]: b, ~: c}"), ("? &x a\n: b\n: c\n", "{a: b, ~: c}"), ("# c\n: v\n", "{~: v}"),
     ("? ? a\n  : b\n: c\n: d\n", "{{a: b}: c, ~: d}"), ("? a\n:\n  : v\n", "{a: {~: v}}"), ("- ? a\n  : b\n  : c\n", "[{a: b, ~: c}]")]
  let misshaped := landings.filter (fun (i, e) => rootShape i != e)
  let shaped := landings.length - misshaped.length
  let mut eligible := 0
  let mut ineligible := 0
  let mut same := 0
  let mut shrank := 0
  let mut grew := 0
  let mut qPauses := 0
  let mut qAdded := 0
  for (input, _) in landings do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          let pre := markedColsOf s.pendingKeys s.indentColumns
          let mid := markedColsOf sP.pendingKeys sP.indentColumns
          let after := markedColsOf sN.pendingKeys sN.indentColumns
          if sP.flowLevel == 0 && c == ':' then
            eligible := eligible + 1
            if after == pre then same := same + 1
            else if after.all (· ∈ pre) then shrank := shrank + 1
            else grew := grew + 1
          else
            ineligible := ineligible + 1
          if sP.flowLevel == 0 && c == '?' then
            qPauses := qPauses + 1
            if sP.col ∈ after && !(sP.col ∈ mid) then qAdded := qAdded + 1
          s := sN
        | _ => break
      | _ => break
  check state s!"P81 colon_open_map's h_kslot relayed (item 417): eligible block `:` steps={eligible} (ineligible pauses={ineligible}) — over s → s': marks unchanged={same} shrank (the answered `?`'s mark popped; still ⊆)={shrank} grew={grew} (must be 0: a `:` adds no mark); `?` pauses={qPauses} adding their own column={qAdded} (negative control, must be all); `:`-landing values composed as predicted (whole value, nested)={shaped}/{landings.length} (misshaped, input ↦ got: {misshaped.map (fun (i, _) => (i, rootShape i))})"
    (eligible > 0 && grew == 0 && qPauses > 0 && qAdded == qPauses && misshaped.isEmpty)

section HeldChainGrammar
open L4YAML.Surface L4YAML.Proofs.RegisterWitness L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction

-- Priority 82 (item 418, PAID), the grammar half of the three held-chain relays.
-- (i) the `-` landing's content IS the slot's `[185]` collection one column left: the entries the
-- landed `-` opens (its body and compact tail) are `SBlockSeqEntries k`, and `slotLandedSeq`
-- reads them as `SBlockIndented nv .blockOut` for every `nv ≤ k` — the hypothesis the held
-- slot line (`hkv`) and ancestor lines (`kvU`) consume.
example (nv k : Nat) (hnk : nv ≤ k) (sp_scan sp_mid sp_ind sp_dash sp_body sp_e : SurfPos)
    (h_ssl : SSLComments sp_scan sp_mid) (h_ind : SIndent k sp_mid sp_ind)
    (h_dash : GLit '-' sp_ind sp_dash) (h_gnot : GNot SNsChar sp_dash)
    (h_body : SBlockIndented k .blockIn sp_dash sp_body) (h_tail : SCompactSeqTail k sp_body sp_e) :
    SBlockIndented nv .blockOut sp_scan sp_e :=
  slotLandedSeq hnk h_ssl (SBlockSeqEntries_of_compactTail h_ind h_dash h_gnot h_body h_tail)

-- (ii) the pay's term shape: the held list `nv :: nsU` with its cover is the `∃ ns` the twin
-- (`h_kslotUp`) owes, and `relay` turns the same pair into the own form (`h_kslot`) — so the
-- twin carries strictly what the own form already spent; nothing new is owed.
example (s' : L4YAML.Scanner.ScannerState) (nv : Nat) (nsU : List Nat) (P : Nat → Prop)
    (hdom : MarkedColsIn s' (nv :: nsU)) (kv : P nv) (kvU : ∀ x ∈ nsU, P x) :
    (∃ ns, MarkedColsIn s' ns ∧ ∀ x ∈ ns, P x) ∧ ∀ x ∈ markedCols s', P x :=
  have chain : ∀ x ∈ nv :: nsU, P x := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact kv
    · exact kvU x hx'
  ⟨⟨nv :: nsU, hdom, chain⟩, MarkedColsIn.relay hdom chain⟩

-- (iii) the cover crosses the `-`: a non-`?` block indicator adds no mark (`h_mcstep_ne`), so the
-- pre-state's cover of the held list is the post-state's — the `∃ ns` is stated at `s'`.
example (sc s' : L4YAML.Scanner.ScannerState) (ns : List Nat) (hdom : MarkedColsIn sc ns)
    (h_mcstep_ne : '-' ≠ '?' → ∀ ns : List Nat, MarkedColsIn sc ns → MarkedColsIn s' ns) :
    MarkedColsIn s' ns :=
  h_mcstep_ne (by decide) ns hdom

-- (iv) the `?`/`:` landing: the chain over the landed `[188]` entry from the chain over the slot's
-- content (`slotChainMap`, the term the undomained twin already spent), for the consed list.
example (nv k : Nat) (hnk : nv + 1 ≤ k) (nsU : List Nat) (sp_start sp_scan sp_mid sp_ind : SurfPos)
    (h_ssl : SSLComments sp_scan sp_mid) (h_ind : SIndent k sp_mid sp_ind)
    (kv : ∀ sp_m : SurfPos, SBlockIndented nv .blockOut sp_scan sp_m → ExplValueLine sp_start nv sp_m)
    (kvU : ∀ x ∈ nsU, ∀ sp_m : SurfPos, SBlockIndented nv .blockOut sp_scan sp_m → ExplValueLine sp_start x sp_m) :
    ∀ x ∈ nv :: nsU, ∀ sp_v : SurfPos, SBlockMapEntry k sp_ind sp_v → ExplValueLine sp_start x sp_v :=
  slotChainMap hnk h_ssl h_ind (by
    rintro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact kv
    · exact kvU x hx')

-- Refutation bucket: with the slot's own line HELD and the ancestor list DECLINED, `[nv]` is the
-- only list the writer can name — and `MarkedColsIn s' [nv]` says every mark is `nv`, which a
-- second marked column refutes.  That case therefore carries the alternative instead of a list;
-- stated as the obligation the singleton would owe.
example (s' : L4YAML.Scanner.ScannerState) (nv : Nat) (hdom : MarkedColsIn s' [nv]) :
    ∀ x ∈ markedCols s', x = nv :=
  MarkedColsIn.relay hdom (fun x hx => by simpa using hx)

-- (v) the third pay, `pendingBlock`'s landed-`?` arm with the own line HELD and the ancestor list
-- DECLINED: the projection itself is the list (`MarkedColsIn.self`), so the own line alone
-- discharges the `∃ ns` — the arm that wrote `Or.inr trivial` owed nothing it did not hold.
example (sc : L4YAML.Scanner.ScannerState) (P : Nat → Prop) (kslot : ∀ nv ∈ markedCols sc, P nv) :
    ∃ ns, MarkedColsIn sc ns ∧ ∀ x ∈ ns, P x :=
  ⟨markedCols sc, MarkedColsIn.self sc, kslot⟩
end HeldChainGrammar

def testHeldChainRelay (state : IO.Ref TestCollector) : IO Unit := do
  -- 82 (item 418, PAID) — the scanner half of the three held-chain relays: at a block `-`, `?` or
  -- `:` landing the mark step the pays carry the held list across (`h_mcstep_ne`) says the step
  -- adds no mark — read over the WHOLE step `s → s'` on the eligible pauses (block-level `-`/`:`;
  -- a `?` adds its own column and is the negative control).  The class the pays make informative
  -- is the landing under a held ANCESTOR list (`nsU ≠ []`): a pause standing under two or more
  -- marks — counted, and read as the refutation of the singleton cover (`[nv]` cannot cover two
  -- marks).  End to end: each closed-`?`-then-`-`/`?`/`:` landing under an enclosing `?` is paired
  -- with the WHOLE value it must compose to (`p81Shape`); every row must hold.
  let rootShape (input : String) : String := match parseYaml input with
    | .ok docs =>
      if docs.size != 1 then s!"docs {docs.size}" else (docs[0]?.map (fun d => p81Shape d.value)).getD "no doc"
    | .error _ => "refused"
  let landings : List (String × String) :=
    [("?\n- a\n: w\n", "{[a]: w}"), ("?\n  ?\n  - a\n  : b\n: c\n", "{{[a]: b}: c}"),
     ("?\n  ?\n  - a\n  - b\n  : c\n: d\n", "{{[a, b]: c}: d}"), ("?\n  ?\n  ? a\n  : b\n: c\n", "{{~: ~, a: b}: c}"),
     ("?\n  ?\n  : b\n: c\n", "{{~: b}: c}"), ("? - a\n: b\n", "{[a]: b}"), ("?\n  - ? a\n    : b\n: c\n", "{[{a: b}]: c}"),
     ("?\n  ?\n    ?\n    - a\n    : b\n  : c\n: d\n", "{{{[a]: b}: c}: d}"), ("- ?\n  - a\n  : b\n", "[{[a]: b}]"),
     ("k:\n  ?\n  - a\n  : b\n", "{k: {[a]: b}}"), ("?\n  ?\n  - a\n  : b\n  : c\n: d\n", "{{[a]: b, ~: c}: d}"),
     ("?\n  ? x\n  : y\n  ?\n  - a\n  : b\n: c\n", "{{x: y, [a]: b}: c}"), ("?\n  ?\n  - a\n: c\n", "{{[a]: ~}: c}"),
     ("?\n  ?\n  ?\n  - a\n  : b\n: c\n", "{{~: ~, [a]: b}: c}"), ("?\n  ?\n  - a\n  ? b\n  : c\n: d\n", "{{[a]: ~, b: c}: d}")]
  let misshaped := landings.filter (fun (i, e) => rootShape i != e)
  let shaped := landings.length - misshaped.length
  let mut dashSteps := 0
  let mut colonSteps := 0
  let mut ineligible := 0
  let mut same := 0
  let mut shrank := 0
  let mut grew := 0
  let mut underTwo := 0
  let mut qPauses := 0
  let mut qAdded := 0
  -- Reachability of the three PAID branches, read off the state the pays read: `mid` is the
  -- register AFTER the preprocess (the dedent closes) and BEFORE the indicator's dispatch, so its
  -- marks are the `nv` / `n` the branch guards compare with the landing column `k`.
  -- (A) `closeThenBlock`'s `-`: every surviving mark `≤ k` is the paid arm (`nv ≤ k`), a mark
  -- `> k` would be the residual `else` birth; two or more marks = the held ancestor list.
  -- (B) `closeThenBlock`'s `?`/`:`: innermost mark `+ 1 ≤ k` is the paid arm, `= k` the `else`.
  -- (C) `pendingBlock`'s landed `?` (no frame closes): innermost `+ 1 ≤ k` paid, `= k` the `else`.
  let mut aPaid := 0
  let mut aAnc := 0
  let mut aBirth := 0
  let mut bPaid := 0
  let mut bBirth := 0
  let mut bDeep := 0
  let mut cPaid := 0
  let mut cBirth := 0
  let mut cDeep := 0
  let reachInputs : List String :=
    ["k:\n  ? a\n  : b\n", "? a\n? b\n: c\n", "?\n  ? a\n  ? b\n: c\n", "- ? a\n  : b\n- ? c\n  : d\n",
     "?\n  ?\n    - a\n  ? b\n  : c\n: d\n", "?\n  k:\n    - a\n  ? b\n: c\n",
     -- (A)'s witnesses: a `-` that closes a deeper sequence and lands under one / two surviving `?` marks
     "?\n  - a\n  -\n    - x\n  - b\n: c\n", "?\n  ?\n    - a\n    -\n      - x\n    - b\n  : c\n: d\n",
     "?\n  ?\n    - a\n    - k:\n        - x\n    - b\n  : c\n: d\n", "- ?\n    -\n      - x\n    - b\n  : c\n"]
  for input in landings.map (·.1) ++ reachInputs do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          let pre := markedColsOf s.pendingKeys s.indentColumns
          let mid := markedColsOf sP.pendingKeys sP.indentColumns
          let after := markedColsOf sN.pendingKeys sN.indentColumns
          if sP.flowLevel == 0 && (c == '-' || c == ':') then
            if c == '-' then dashSteps := dashSteps + 1 else colonSteps := colonSteps + 1
            if after == pre then same := same + 1
            else if after.all (· ∈ pre) then shrank := shrank + 1
            else grew := grew + 1
            if pre.eraseDups.length ≥ 2 then underTwo := underTwo + 1
          else
            ineligible := ineligible + 1
          if sP.flowLevel == 0 && c == '?' then
            qPauses := qPauses + 1
            if sP.col ∈ after && !(sP.col ∈ mid) then qAdded := qAdded + 1
          if sP.flowLevel == 0 && (c == '-' || c == '?' || c == ':') then
            let k := sP.col
            let closing := sP.indentColumns.size < s.indentColumns.size
            let marks := mid.eraseDups
            match marks.max? with
            | some n =>
              if closing && c == '-' then
                if marks.all (· ≤ k) then
                  aPaid := aPaid + 1
                  if marks.length ≥ 2 then aAnc := aAnc + 1
                else aBirth := aBirth + 1
              else if closing then
                if n + 1 ≤ k then bPaid := bPaid + 1
                else if n == k then bBirth := bBirth + 1
                else bDeep := bDeep + 1
              else if c == '?' then
                if n + 1 ≤ k then cPaid := cPaid + 1
                else if n == k then cBirth := cBirth + 1
                else cDeep := cDeep + 1
            | none => pure ()
          s := sN
        | _ => break
      | _ => break
  check state s!"P82 held-chain relays (item 418): eligible block `-` steps={dashSteps} `:` steps={colonSteps} (ineligible pauses={ineligible}) — over s → s': marks unchanged={same} shrank={shrank} grew={grew}; under two or more marks (ancestor list held, singleton cover refuted)={underTwo}; `?` pauses={qPauses} add their own column={qAdded}; closed-`?` landings composed as predicted (whole value, nested)={shaped}/{landings.length}{if misshaped.isEmpty then "" else s!" misshaped: {misshaped.map (fun (i, e) => s!"{i.quote} ↦ {rootShape i} (predicted {e})")}"} REACHED — (A) `-` after a close: paid arm={aPaid} (under a held ancestor list={aAnc}) residual birth={aBirth}; (B) `?`/`:` after a close: paid={bPaid} own-column else={bBirth} deeper={bDeep}; (C) landed `?` on a pending block: paid={cPaid} own-column else={cBirth} deeper={cDeep}"
    (dashSteps > 0 && colonSteps > 0 && grew == 0 && underTwo > 0 && qPauses > 0 && qAdded == qPauses && misshaped.isEmpty &&
      aPaid > 0 && aAnc > 0 && aBirth == 0 && bPaid > 0 && bDeep == 0 && cPaid > 0 && cDeep == 0)

-- Priority 83 (item 422, PAID): Rule 2 for the openers' `h_outer` body — at every block `:` and compact
-- `?` pause that closes a `?` park, the prepared register is K7 (only the landing column `k = sP.col`
-- is marked — `refused_of_outer_disp`'s side) or ARMED (some marked column `≠ k` — the new right arm):
-- `exists_mem_ne_of_not_markedColsIn` is the decision, so a pause in NEITHER bucket would be a dead
-- register at a sound block state (item 410's `refused_of_markedCols_eq_nil` refutes it).  Second half:
-- the key the body carries — at K7 pauses the prepared save sits at the landing column (`hkey`), on
-- either side of `h_park` (`simpleKeyAllowed` down at the park, up at the landing: `landing_or_park_save`).
-- Third half: an ARMED witness survives the `:` dispatch (the `-`/flow pauses are negative controls).
def testArmedOuterPartition (state : IO.Ref TestCollector) : IO Unit := do
  let inputs : List String :=
    [ "? a\n: b", "? a\n: b\n? c\n: d", "- ? a\n  : b", "- ? a\n  : b\n- ? c\n  : d",
      "k:\n  ? a\n  : b", "? ? a\n  : b\n: c", "? - a\n: b", "? : v\n: w", "- ? : v",
      "? &a k\n: v", "- ? &a\n  : v", "? !!str a\n: b", "? a\n? b\n: c",
      "k:\n  ? a\n: b", "k:\n  - ? a\n    : b\n  ? c\n  : d", "? a\n  b\n: c",
      "a: 1\n? b\n: 2", "- a\n- ? b\n  : c", "? [a]\n: b", "? {a: 1}\n: b",
      "[? a : b]", "{? a : b}", "- a\n- b", "a: [b, c]\n? d\n: e" ]
  let mut colonPauses := 0
  let mut qPauses := 0
  let mut k7 := 0
  let mut armed := 0
  let mut neither := 0
  let mut armedWitnesses : List (Nat × Nat) := []
  let mut skaDownAtPark := 0
  let mut keyAtLanding := 0
  let mut keyElsewhere := 0
  let mut witnessSurvived := 0
  let mut witnessClosed := 0
  let mut flowPauses := 0
  let mut dashPauses := 0
  let mut parsed := 0
  for input in inputs do
    match parseYaml input with
    | .ok _ => parsed := parsed + 1
    | .error _ => pure ()
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          let mid := (markedColsOf sP.pendingKeys sP.indentColumns).eraseDups
          let after := markedColsOf sN.pendingKeys sN.indentColumns
          let k := sP.col
          if sP.flowLevel == 0 && (c == ':' || c == '?') && !mid.isEmpty then
            if c == ':' then colonPauses := colonPauses + 1 else qPauses := qPauses + 1
            if s.simpleKeyAllowed == false then skaDownAtPark := skaDownAtPark + 1
            match mid.find? (· != k) with
            | some x =>
              armed := armed + 1
              armedWitnesses := (k, x) :: armedWitnesses
              if x ∈ after then witnessSurvived := witnessSurvived + 1 else witnessClosed := witnessClosed + 1
            | none =>
              if mid == [k] then
                k7 := k7 + 1
                if sP.simpleKey.possible then
                  if sP.simpleKey.pos.col == k then keyAtLanding := keyAtLanding + 1
                  else keyElsewhere := keyElsewhere + 1
                else keyAtLanding := keyAtLanding + 1
              else neither := neither + 1
          else if sP.flowLevel > 0 && (c == ':' || c == '?') then flowPauses := flowPauses + 1
          else if sP.flowLevel == 0 && c == '-' then dashPauses := dashPauses + 1
          s := sN
        | _ => break
      | _ => break
  let witnesses := armedWitnesses.reverse.eraseDups
  check state s!"P83 armed-outer partition (item 422): closing-`:` pauses={colonPauses} compact-`?` pauses={qPauses}; K7={k7} ARMED={armed} neither={neither}; K7 key at landing={keyAtLanding} elsewhere={keyElsewhere}; simpleKeyAllowed down at park={skaDownAtPark}; ARMED witness survived `:`={witnessSurvived} closed={witnessClosed}; controls flow={flowPauses} dash={dashPauses}; parsed={parsed}/{inputs.length}; witnesses (k, x)={witnesses}"
    (colonPauses > 0 && qPauses > 0 && neither == 0 && k7 > 0 && armed ≥ 3 && keyElsewhere == 0 &&
     skaDownAtPark > 0 && flowPauses > 0 && dashPauses > 0 && witnessClosed == 0 &&
     witnesses.all (fun (k, x) => x != k))

-- Priority 83b (item 422, review): the membership lemma's OWN refutation half — `exists_mem_ne_of_not_markedColsIn`
-- tested as an implication over CONSTRUCTED registers, not over scanned ones: `pendingKeys` / `indentColumns` varied
-- independently (no marks; one mark at `k`; one away; several; a `some none` slot; an unmarked slot at another column;
-- a key with NO indent column — the mismatched-length case `markedCols_mem` reads as `none`).  The hypothesis
-- `¬ MarkedColsIn s [k]` is decided from the arrays (some marked slot's column `≠ k`); a hypothesis-true register with no
-- witness `≠ k` in `markedColsOf` refutes the lemma, and a hypothesis-false one WITH a witness refutes its converse.
def testArmedOuterLemma (state : IO.Ref TestCollector) : IO Unit := do
  let base := L4YAML.Scanner.ScannerState.mk' ""
  let mkS (pks : Array (Option Nat)) (cols : Array Int) : L4YAML.Scanner.ScannerState :=
    { base with pendingKeys := pks, indents := cols.map fun c => { column := c, isSequence := false } }
  let cases : List (String × Array (Option Nat) × Array Int) :=
    [ ("no slots", #[], #[]),
      ("one unmarked slot", #[none], #[0]),
      ("one mark at k", #[some 3], #[2]),
      ("one mark away", #[some 3], #[0]),
      ("two marks both k", #[some 1, some 4], #[2, 2]),
      ("k and away", #[some 1, some 4], #[2, 5]),
      ("away and away", #[some 1, some 4], #[0, 5]),
      ("mark at k, unmarked away", #[some 1, none], #[2, 7]),
      ("unmarked at k, mark away", #[none, some 9], #[2, 6]),
      ("mark with no column", #[some 1], #[]),
      ("mark at k, second mark with no column", #[some 1, some 2], #[2]),
      ("negative column mark (toNat 0) with k = 2", #[some 1], #[-3]),
      ("three marks, middle away", #[some 1, some 2, some 3], #[2, 0, 2]) ]
  let k : Nat := 2
  let mut hypTrue := 0
  let mut hypFalse := 0
  let mut refuted : List String := []
  let mut converseRefuted : List String := []
  for (name, pks, cols) in cases do
    let s := mkS pks cols
    let marks := markedColsOf s.pendingKeys s.indentColumns
    -- ¬ MarkedColsIn s [k]  ⇔  some slot i has pks[i] = some (some _), cols[i] = some c, c.toNat ≠ k
    let hyp := (List.range pks.size).any fun i =>
      match pks[i]?, cols[i]? with
      | some (some _), some c => c.toNat != k
      | _, _ => false
    let witness := marks.find? (· != k)
    if hyp then
      hypTrue := hypTrue + 1
      if witness.isNone then refuted := name :: refuted
    else
      hypFalse := hypFalse + 1
      if witness.isSome then converseRefuted := name :: converseRefuted
  check state s!"P83b exists_mem_ne_of_not_markedColsIn on constructed registers (item 422): cases={cases.length} hypothesis-true={hypTrue} hypothesis-false={hypFalse}; refuted={refuted} converse-refuted={converseRefuted}"
    (hypTrue == 6 && hypFalse == 7 && refuted.isEmpty && converseRefuted.isEmpty)

/-! **Priority 84 — the (β-mark) body is a tautology on the sound block domain** (item 424).  The
    body item 423 priced, `ExplicitValueRefused sc ∨ markedCols sc ≠ []`, is INHABITED at every sound
    block state: item 410's `refused_of_markedCols_eq_nil` reads a markless register as dead, and a
    non-markless one is the other arm.  A `PackAlt` write of this body says nothing a `trivial` did
    not — the `∨ True` smell under another name — so the pay is REFUTED before it is made.  An
    `example`, not a declaration: a refutation feeds no capstone (Rule 1), it only has to be checked
    by the build (§1). -/
example {s : L4YAML.Scanner.ScannerState} (hs : L4YAML.Proofs.PendingKeySound.Sound s)
    (hfl : s.flowLevel = 0) :
    s.explicitKeyLine = none ∨ L4YAML.Proofs.RegisterWitness.markedCols s ≠ [] :=
  match h : L4YAML.Proofs.RegisterWitness.markedCols s with
  | [] => Or.inl (L4YAML.Proofs.RegisterWitness.refused_of_markedCols_eq_nil hs hfl h)
  | _ :: _ => Or.inr (by simp)

/-- Priority 84's register half (Devin Review on the PR): the `example` quantifies over EVERY sound
    block state, not the scanned ones, so the body is checked on hand-built registers with the `Sound`
    hypothesis DECIDED by a Bool mirror of its four clauses (`SlotsOk`, `RegOk`, `BaseOk`, `StackOk`) —
    a hypothesis-true register without the conclusion refutes; a hypothesis-FALSE register without it
    (a markless slot array beside a LIVE register — `RegOk` fails) shows the `Sound` premise is
    load-bearing, not decoration. -/
def testPackAltMarkTautoRegisters (state : IO.Ref TestCollector) : IO Unit := do
  let base := L4YAML.Scanner.ScannerState.mk' ""
  let mkS (pks : Array (Option Nat)) (cols : Array Int) (ekl : Option Nat) (ekc : Int) (fl : Nat)
      (stack : Array (Option Nat × Int)) : L4YAML.Scanner.ScannerState :=
    { base with pendingKeys := pks, indents := cols.map fun c => { column := c, isSequence := false },
                explicitKeyLine := ekl, explicitKeyCol := ekc, flowLevel := fl, explicitKeyStack := stack }
  let soundB (t : L4YAML.Scanner.ScannerState) : Bool :=
    let slots := t.pendingKeys.size == t.indents.size &&
      (List.range t.pendingKeys.size).all fun i =>
        (match t.pendingKeys[i]?, t.indentColumns[i]? with
          | some (some _), some c => decide (0 ≤ c)
          | some (some _), none => false
          | _, _ => true)
    let inner := t.innermostPendingKey
    let reg := t.flowLevel != 0 || (t.explicitKeyLine == inner.1 && t.explicitKeyCol == inner.2)
    let baseOk := t.flowLevel == 0 || t.explicitKeyStack[0]? == some inner
    let stackOk := t.explicitKeyStack.size == t.flowLevel
    slots && reg && baseOk && stackOk
  let cases : List (String × L4YAML.Scanner.ScannerState) :=
    [ ("empty, dead register", mkS #[] #[] none (-1) 0 #[]),
      ("one unmarked slot, dead register", mkS #[none] #[0] none (-1) 0 #[]),
      ("one mark at 2, register reads it", mkS #[some 3] #[2] (some 3) 2 0 #[]),
      ("nested: marks at 0 and 2, register reads the inner", mkS #[some 1, some 3] #[0, 2] (some 3) 2 0 #[]),
      ("nested: outer mark only, inner unmarked, register reads the outer", mkS #[some 1, none] #[0, 2] (some 1) 0 0 #[]),
      ("one mark, register reads ANOTHER line (RegOk fails)", mkS #[some 3] #[2] (some 7) 2 0 #[]),
      ("markless beside a LIVE register (RegOk fails) — the body is FALSE here", mkS #[none] #[0] (some 3) 0 0 #[]),
      ("markless, live register, no slots at all — the body is FALSE here", mkS #[] #[] (some 1) 0 0 #[]),
      ("mark on a negative column (SlotsOk fails)", mkS #[some 2] #[-1] (some 2) (-1) 0 #[]),
      ("slot arrays out of lockstep (SlotsOk fails)", mkS #[some 2, none] #[2] (some 2) 2 0 #[]),
      ("in flow (flowLevel 1), dead register, stack holds the innermost", mkS #[none] #[0] none (-1) 1 #[(none, -1)]),
      ("in flow, armed below the open", mkS #[some 2] #[2] (some 2) 2 1 #[(some 2, 2)]) ]
  let mut hypTrue := 0
  let mut hypFalse := 0
  let mut refuted : List String := []
  let mut soundNecessary := 0
  let mut refusedArm := 0
  let mut armedArm := 0
  for (name, t) in cases do
    let marks := markedColsOf t.pendingKeys t.indentColumns
    let conclusion := t.explicitKeyLine.isNone || !marks.isEmpty
    if soundB t && t.flowLevel == 0 then
      hypTrue := hypTrue + 1
      if conclusion then
        if t.explicitKeyLine.isNone then refusedArm := refusedArm + 1
        else armedArm := armedArm + 1
      else refuted := name :: refuted
    else
      hypFalse := hypFalse + 1
      if !conclusion then soundNecessary := soundNecessary + 1
  check state s!"P84b (β-mark) body on constructed registers (item 424): cases={cases.length} hypothesis-true={hypTrue} (refused arm={refusedArm}, armed arm={armedArm}) hypothesis-false={hypFalse}; refuted={refuted}; hypothesis-false registers where the body FAILS (Sound is load-bearing)={soundNecessary}"
    (hypTrue == 5 && hypFalse == 7 && refuted.isEmpty && refusedArm == 2 && armedArm == 3 && soundNecessary == 2)

/-- The scan half of Priority 84: at every block pause of P83's corpus (plus two dedent shapes) the
    decided dichotomy — refused (`explicitKeyLine = none`) or armed (a marked slot) — is checked on the
    PREPARED state; `neither` must be 0 (the lemma), both arms must be reached, and `markLost` counts the
    pauses where the park held a mark the preprocess CLOSED (a dedent) and the refusal arm caught the
    body — the (β-mark) transports would be paid by the tautology at `s_prep`, never by a mark that
    survives, which is what makes the body uninformative. -/
def testPackAltMarkTauto (state : IO.Ref TestCollector) : IO Unit := do
  let inputs : List String :=
    [ "? a\n: b", "? a\n: b\n? c\n: d", "- ? a\n  : b", "k:\n  ? a\n  : b", "? ? a\n  : b\n: c",
      "? : v\n: w", "? &a k\n: v", "? !!str a\n: b", "? a\n? b\n: c", "k:\n  ? a\n: b",
      "k:\n  - ? a\n    : b\n  ? c\n  : d", "a: 1\n? b\n: 2", "- a\n- ? b\n  : c", "? [a]\n: b",
      "- a\n- b", "a: [b, c]\n? d\n: e", "k:\n  ? a\nb: c", "k:\n  - ? a\n    : b\nz: 1" ]
  let mut pauses := 0
  let mut refusedOnly := 0
  let mut armedOnly := 0
  let mut both := 0
  let mut neither := 0
  let mut markLost := 0
  let mut parsed := 0
  for input in inputs do
    match parseYaml input with
    | .ok _ => parsed := parsed + 1
    | .error _ => pure ()
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, _)) =>
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          if sP.flowLevel == 0 then
            pauses := pauses + 1
            let before := markedColsOf s.pendingKeys s.indentColumns
            let marks := markedColsOf sP.pendingKeys sP.indentColumns
            let refused := sP.explicitKeyLine.isNone
            match refused, marks.isEmpty with
            | true, true => refusedOnly := refusedOnly + 1
            | false, false => armedOnly := armedOnly + 1
            | true, false => both := both + 1
            | false, true => neither := neither + 1
            if !before.isEmpty && marks.isEmpty && refused then markLost := markLost + 1
          s := sN
        | _ => break
      | _ => break
  check state s!"P84 (β-mark) body on prepared block states (item 424): pauses={pauses} refused-only={refusedOnly} armed-only={armedOnly} both={both} NEITHER={neither}; mark closed by the preprocess and caught by the refusal arm={markLost}; parsed={parsed}/{inputs.length}"
    (pauses > 0 && refusedOnly > 0 && armedOnly > 0 && neither == 0 && markLost > 0)

/-! **Priority 85 — (ζ-dedent) refuted before the proof** (item 429).  Item 428's NEXT named the
    missing scanner fact as "a dedent that under-runs the frames EMPTIES the register".  Rule 2 on the
    scanner says no: a mark at an ENCLOSING `?` park survives every dedent that lands above it
    (`? - a\n  - b: c\n  - d\n: e` — the `-` lands at column 2 on a sequence frame, `map 2` names no
    frame, and the `?` mark at column 0 is still set), so `survivedUnderRun` must be POSITIVE.  What
    does hold at every block pause — the strongest true statement, proven in scratch over `Sound`,
    `Mono`, `SentinelBase` and the popped stack — is that every surviving mark sits at or below the
    landing column (`leViol = 0`) and was a mark before the preprocess (`subViol = 0`); the slot of a
    sequence frame is never marked (`seqTopMarked = 0`), an invariant no `Sound` clause states.
    `underRun` is the item 297 arm's exact shape — a popped landing whose stack top is a SEQUENCE
    entry AT the landing column (`preprocess_landing_mem_or_seq`'s right disjunct) — not merely a
    sequence top. -/
def testDedentMarksSurvive (state : IO.Ref TestCollector) : IO Unit := do
  let inputs : List String :=
    [ "? a\n: b", "? a\n: b\n? c\n: d", "- ? a\n  : b", "k:\n  ? a\n  : b", "? ? a\n  : b\n: c",
      "? : v\n: w", "? &a k\n: v", "? !!str a\n: b", "? a\n? b\n: c", "k:\n  ? a\n: b",
      "k:\n  - ? a\n    : b\n  ? c\n  : d", "a: 1\n? b\n: 2", "- a\n- ? b\n  : c", "? [a]\n: b",
      "- a\n- b", "a: [b, c]\n? d\n: e", "k:\n  ? a\nb: c", "k:\n  - ? a\n    : b\nz: 1",
      "? - a\n  - ? b\n    : c\n  - d\n: e", "? a\n:\n  - ? b\n    : c\n  - d\nz: 1", "? - a\n  - b: c\n  - d\n: e",
      "- a\n? b\n: c", "- a\n- ? b\n  : c\n? d\n: e", "?\n  ? a\n  : b\n: c\nz: 1", "? - ? a\n    : b\n  - c\n: d",
      "a:\n  ? b\n  : c\n  ? d\n  : e\nz: 1", "? a\n: b\nkey: v", "a:\n  - ? b\n    : c\n  - key: v",
      "? - a\n  -\n    ? b\n    : c\n  - d\n: e" ]
  let mut pauses := 0
  let mut pops := 0
  let mut underRun := 0
  let mut survivedUnderRun := 0
  let mut leViol := 0
  let mut subViol := 0
  let mut seqTopMarked := 0
  for input in inputs do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:80] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, _)) =>
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          if sP.flowLevel == 0 then
            pauses := pauses + 1
            let before := L4YAML.Proofs.RegisterWitness.markedCols s
            let after := L4YAML.Proofs.RegisterWitness.markedCols sP
            if !(after.all (before.contains ·)) then subViol := subViol + 1
            if !(after.all (· ≤ sP.col)) then leViol := leViol + 1
            let topSeq := match sP.indents.back? with
              | some e => e.isSequence && e.column == (sP.col : Int)
              | none => false
            match sP.indents.back?, sP.pendingKeys[sP.indents.size - 1]? with
            | some e, some (some _) => if e.isSequence then seqTopMarked := seqTopMarked + 1
            | _, _ => pure ()
            if sP.indents.size < s.indents.size then
              pops := pops + 1
              if topSeq then
                underRun := underRun + 1
                if !after.isEmpty then survivedUnderRun := survivedUnderRun + 1
          s := sN
        | _ => break
      | _ => break
  check state s!"P85 (ζ-dedent) refuted on the scanner (item 429): pauses={pauses} pops={pops} under-run landings={underRun} marks SURVIVING an under-run={survivedUnderRun} le-violations={leViol} subset-violations={subViol} seq-top marked={seqTopMarked}"
    (pauses > 0 && pops > 0 && underRun > 0 && survivedUnderRun > 0 && leViol == 0 && subViol == 0 && seqTopMarked == 0)

/-! **Priority 86 — (ι-floor) refuted, and the seq-top key read at the dispatch** (item 430).  The
    frame arms' cover `Floor lo n ks ∧ Covered lo ks sc` stands at the park's own index (`Floor n n []`)
    or at the root (`Floor 0 k []`), so a mark BELOW the floor is a mark below the stack top after the
    landing — an enclosing `?` park's.  `belowTop` and `belowLanding` must equal `survivors` (every
    mark surviving an under-run landing sits strictly below the top's column and below the landing
    column) and be positive.  What the scanner can pin is the LOWER half of the link — the survivors
    lie below the landing column, hence below any floor `lo ≥ s_prep.col`; that the producers' floors
    never fall below the park's index (`Floor n n []`, the root literal, `Floor.mono_index` only
    raising) is the cover READING in DOCS 430, not this test.  The second half reads the item 297
    arm's reachability: a key landing on a sequence frame's own column PASSES
    `scanNextToken_dispatchContent` (`dispatchOk = keyOnSeqTop`) and the input is rejected ON THE
    `:` STEP — the scan step whose preprocessed character is `:` fails with `trailingContent`
    (`atSequenceIndent`, §8.2.1); any other failure, position or cause does not count
    (`laterErrors = inputsWithKeyOnSeqTop`) — so the arm is reached with `h_dispatch = .ok` and
    `SeqTopKey` is its honest alternative. -/
def testMarkFloorAndSeqTopKey (state : IO.Ref TestCollector) : IO Unit := do
  let underRunInputs : List String :=
    [ "? - a\n  - ? b\n    : c\n  - d\n: e", "? a\n:\n  - ? b\n    : c\n  - d\nz: 1", "? - a\n  - b: c\n  - d\n: e",
      "? - ? a\n    : b\n  - c\n: d", "a:\n  - ? b\n    : c\n  - key: v", "? - a\n  -\n    ? b\n    : c\n  - d\n: e",
      "k:\n  - ? a\n    : b\nz: 1", "- a\n- ? b\n  : c" ]
  let mut underRun := 0
  let mut survivors := 0
  let mut belowTop := 0
  let mut belowLanding := 0
  for input in underRunInputs do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:80] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, _)) =>
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          if sP.flowLevel == 0 && sP.indents.size < s.indents.size then
            match sP.indents.back? with
            | some e =>
              if e.isSequence && e.column == (sP.col : Int) then
                underRun := underRun + 1
                let marks := L4YAML.Proofs.RegisterWitness.markedCols sP
                if !marks.isEmpty then
                  survivors := survivors + 1
                  if marks.all (fun nv => (nv : Int) < e.column) then belowTop := belowTop + 1
                  if marks.all (fun nv => nv < sP.col) then belowLanding := belowLanding + 1
            | none => pure ()
          s := sN
        | _ => break
      | _ => break
  let seqTopInputs : List String :=
    [ "- a\nc: d", "? - a\n  -\n    - b\n  c: d\n: e", "k:\n  - a\n  c: d", "- - a\n  c: d", "- a\n- b\nc: d",
      "k:\n  -\n    - a\n  c: d", "- a\n\"c\": d", "- a\n&y c: d", "- a\n- b" ]
  let mut keyOnSeqTop := 0
  let mut dispatchOk := 0
  let mut inputsWithKeyOnSeqTop := 0
  let mut laterErrors := 0
  for input in seqTopInputs do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    let mut sawKey := false
    let mut colonRejects := false
    for _ in [:80] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        let seqTopAt := match sP.indents.back? with
          | some e => e.isSequence && e.column == (sP.col : Int)
          | none => false
        if seqTopAt && c != '-' && c != '#' && c != '?' then
          keyOnSeqTop := keyOnSeqTop + 1
          sawKey := true
          let sD := if sP.allowDirectives then
            { sP with allowDirectives := false, documentEverStarted := true } else sP
          match L4YAML.Scanner.scanNextToken_dispatchContent sD c with
          | .ok _ => dispatchOk := dispatchOk + 1
          | .error _ => pure ()
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) => s := sN
        | .ok none => break
        | .error e =>
          match c, e with
          | ':', .trailingContent _ _ => colonRejects := true
          | _, _ => pure ()
          break
      | .ok none => break
      | .error _ => break
    if sawKey then
      inputsWithKeyOnSeqTop := inputsWithKeyOnSeqTop + 1
      if colonRejects then laterErrors := laterErrors + 1
  check state s!"P86 (ι-floor) refuted / seq-top key reaches the dispatch (item 430): under-run landings={underRun} with surviving marks={survivors} all below the top={belowTop} all below the landing column={belowLanding}; key-on-seq-top pauses={keyOnSeqTop} dispatchContent ok={dispatchOk} inputs={inputsWithKeyOnSeqTop} rejected by `trailingContent` on the `:` step={laterErrors}"
    (underRun > 0 && survivors > 0 && belowTop == survivors && belowLanding == survivors && keyOnSeqTop > 0 && dispatchOk == keyOnSeqTop && inputsWithKeyOnSeqTop > 0 && laterErrors == inputsWithKeyOnSeqTop)

/-! **Priority 87 — (ο-absent): the map frames face's negative arm `NoMapLine` read on the scanner**
    (item 435).  Items 432–434 found the face's outer `∨ True` is a three-valued statement — *the park's
    value line resumes these frames* / *the park has no such line* — written with `True` for the second
    value.  The candidate negative arm is a projection of the scanner state: `NoMapLine sc := sc.currentIndent
    < 0 ∨ (sc.indents.back? = some e ∧ e.isSequence)` — the stack top is the sentinel or a sequence level,
    so no mapping value line is open at the top.  Rule 2 before the proof: at every block-context pause,
    classed by the last real token (none = the virgin park, `---`/`...` = the marker parks, `-` = the entry
    parks, anchor/tag = the props park, `:` = a mapping value line), the arm must HOLD at every virgin,
    marker and entry pause (those writers punt for the right reason) and FAIL at some props pause and at
    every `:` pause (a props park at a mapping value position is not "absent" — its writer must relay the
    face, and the arm is not vacuous).  READ (the pinned numbers): it holds at every virgin and marker
    pause, fails at every `:` pause, fails at 6 of 10 props pauses — and FAILS at the `-` of a sequence
    at the SAME indentation as its key (`a:⏎- b`, YAML's compact block sequence as a mapping value:
    the `-` pushes no sequence level, the top is the mapping at the key's column), the 6 `entryFails`,
    so the entry parks are not "absent" either: at `k:⏎- a` the park's value line IS open and the
    `-` writers hold no face for it (Rule 2's refutation of (ο-absent) for the entry class).  The six
    are pinned by input and position, not by count, so a different failure cannot pass as this one. -/
def testNoMapLineArm (state : IO.Ref TestCollector) : IO Unit := do
  let inputs : List String :=
    [ "a: 1", "- a\n- b", "---\na: 1\n...\n", "--- a\n--- b", "k: !!str\n  v", "k: &x\n  v", "- !!str\n  v",
      "!!str a: b", "k:\n  - a\n  - b", "? a\n: b", "- - a\n  - b", "k:\n  v: w\n  x: y",
      "a:\n  b:\n    c: d\n  e: f", "- a: 1\n  b: 2", "k: [a, b]", "k:\n  [a, b]", "--- !!map\na: 1", "...\n",
      "# c\na: 1", "k: |\n  text\nm: 2", "- &a x\n- *a", "? - a\n: b", "a: !!seq\n- b", "- a\n-\n  - b\n- c",
      "a: &x !!str\n  v\nb: 2", "---\n- a\n---\n- b\n...", "k:\n  !!str v\nm: 1",
      "a:\n- b", "a:\n- b\n- c\nd: 1", "k:\n- x: 1\n  y: 2", "k:\n- - a\n  - b" ]
  let noMapLine (s : L4YAML.Scanner.ScannerState) : Bool :=
    s.currentIndent < 0 || (match s.indents.back? with | some e => e.isSequence | none => false)
  let kindOf (s : L4YAML.Scanner.ScannerState) : String :=
    match L4YAML.Scanner.lastRealToken? s.tokens with
    | none => "virgin"
    | some t => match t.val with
      | .streamStart => "virgin" | .placeholder => "virgin" | .documentStart => "marker" | .documentEnd => "marker"
      | .blockEntry => "entry" | .anchor .. => "props" | .tag .. => "props" | .value => "value"
      | _ => "other"
  let mut pauses : Array Nat := #[0, 0, 0, 0, 0, 0]
  let mut holds : Array Nat := #[0, 0, 0, 0, 0, 0]
  let idx (k : String) : Nat := match k with
    | "virgin" => 0 | "marker" => 1 | "entry" => 2 | "props" => 3 | "value" => 4 | _ => 5
  let mut entryFails : List String := []
  for input in inputs do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:80] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        if sP.flowLevel == 0 && c != '#' then
          let i := idx (kindOf sP)
          pauses := pauses.set! i (pauses[i]! + 1)
          if noMapLine sP then holds := holds.set! i (holds[i]! + 1)
          else if i == 2 then entryFails := entryFails ++ [s!"{repr input}@{sP.line}:{sP.col}"]
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) => s := sN
        | _ => break
      | _ => break
  check state s!"P87 (ο-absent) NoMapLine on the scanner (item 435): virgin={holds[0]!}/{pauses[0]!} marker={holds[1]!}/{pauses[1]!} entry={holds[2]!}/{pauses[2]!} props={holds[3]!}/{pauses[3]!} value={holds[4]!}/{pauses[4]!} other={holds[5]!}/{pauses[5]!} entry-fails={entryFails}"
    (pauses[0]! > 0 && holds[0]! == pauses[0]! && pauses[1]! > 0 && holds[1]! == pauses[1]!
      && pauses[2]! > 0 && holds[2]! + entryFails.length == pauses[2]!
      && entryFails == [ s!"{repr "a: !!seq\n- b"}@1:2", s!"{repr "a:\n- b"}@1:2", s!"{repr "a:\n- b\n- c\nd: 1"}@1:2",
           s!"{repr "a:\n- b\n- c\nd: 1"}@2:2", s!"{repr "k:\n- x: 1\n  y: 2"}@1:2", s!"{repr "k:\n- - a\n  - b"}@1:2" ]
      && pauses[3]! > 0 && holds[3]! < pauses[3]! && pauses[4]! > 0 && holds[4]! == 0)


/-! **Priority 88 — (σ-three-arms): the two new park fields read on the scanner** (item 436).  The
    per-class restatement puts `h_ntop : sc.currentIndent < 0` on the marker parks (`scanDocumentStart` /
    `scanDocumentEnd` call `unwindIndents s (-1)`) and `h_seqTop` on the `-` parks: after the `-` step the
    stack top is a sequence level (`pushSequenceIndent` pushed at the `-`'s column) or, in the compact
    `k:⏎- a` case where it pushed nothing, the mapping level AT the `-`'s own column.  Rule 2 before the
    proof: at every marker pause the sentinel is on top; at every `-` pause the top is a sequence level or
    a mapping level at the `-` column — and NO third case (a mapping top at another column would be an
    indentation the scanner refuses).  The compact pauses are the six P87 pinned. -/
def testThreeArmsFields (state : IO.Ref TestCollector) : IO Unit := do
  let inputs : List String :=
    [ "a: 1", "- a\n- b", "---\na: 1\n...\n", "--- a\n--- b", "k: !!str\n  v", "k:\n  - a\n  - b", "? a\n: b",
      "- - a\n  - b", "k:\n  v: w\n  x: y", "a:\n  b:\n    c: d\n  e: f", "- a: 1\n  b: 2", "--- !!map\na: 1",
      "...\n", "- &a x\n- *a", "? - a\n: b", "a: !!seq\n- b", "- a\n-\n  - b\n- c", "---\n- a\n---\n- b\n...",
      "a:\n- b", "a:\n- b\n- c\nd: 1", "k:\n- x: 1\n  y: 2", "k:\n- - a\n  - b", "%YAML 1.2\n---\na: 1",
      "a:\n  - b\n  -\n    c: d\n---\ne: f", "- a\n...\n- b", "k:\n  - a\n- b" ]
  let mut markerPauses := 0
  let mut markerTop := 0
  let mut entryPauses := 0
  let mut seqTop := 0
  let mut compactTop := 0
  let mut thirdCase : List String := []
  let mut flowClosePauses := 0
  let mut flowCloseSentinel := 0
  for input in inputs ++ ["[a]", "[a]\n---\n{b: c}", "{a: b}\nk: v", "[a, [b]]\n- c"] do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:80] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        if sP.flowLevel == 0 && c != '#' then
          match L4YAML.Scanner.lastRealToken? sP.tokens with
          | some t =>
            match t.val with
            | .flowSequenceEnd | .flowMappingEnd =>
              flowClosePauses := flowClosePauses + 1
              if sP.currentIndent < 0 then flowCloseSentinel := flowCloseSentinel + 1
            | .documentStart | .documentEnd =>
              markerPauses := markerPauses + 1
              if sP.currentIndent < 0 then markerTop := markerTop + 1
            | .blockEntry =>
              entryPauses := entryPauses + 1
              match sP.indents.back? with
              | some e =>
                if e.isSequence then seqTop := seqTop + 1
                else if e.column == (t.pos.col : Int) then compactTop := compactTop + 1
                else thirdCase := thirdCase ++ [s!"{repr input}@{sP.line}:{sP.col}"]
              | none => thirdCase := thirdCase ++ [s!"{repr input}@{sP.line}:{sP.col} (no top)"]
            | _ => pure ()
          | none => pure ()
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) => s := sN
        | _ => break
      | _ => break
  check state s!"P88 (σ-three-arms) park fields on the scanner (item 436): marker sentinel-top={markerTop}/{markerPauses}; entry seq-top={seqTop} compact-top={compactTop} of {entryPauses}; third case={thirdCase}; root flow-close pauses with the sentinel on top={flowCloseSentinel}/{flowClosePauses} (so `h_seqTop` is NOT a `pendingContent` field: review on #244)"
    (markerPauses > 0 && markerTop == markerPauses && entryPauses > 0
      && seqTop + compactTop == entryPauses && compactTop == 6 && thirdCase.isEmpty
      && flowClosePauses > 0 && flowCloseSentinel == flowClosePauses)


-- Review on #250 (item 441): the restated chain alternative `… ∨ markedCols sc ≠ []` is a
-- TAUTOLOGY — the pack's informative arm is vacuous over `[]` exactly where the alternative is
-- false (item 424's lesson in the other direction).  Checked at elaboration as an `example`: a
-- pin on the Prop would be worthless (§7) and a named lemma would feed no capstone (Rule 1).
example (L : List Nat) (P : Nat → Prop) : (∀ nv ∈ L, P nv) ∨ L ≠ [] := by
  cases L with
  | nil => exact Or.inl (fun _ h => by simp at h)
  | cons _ _ => exact Or.inr (by simp)

def testPackAltMarks (state : IO.Ref TestCollector) : IO Unit := do
  -- P90 (item 441, (ω-pay)): the scanner projection proposed for the pack chain's `∨ PackAlt sc`
  -- arm (today `True`) is `RegisterWitness.markedCols sc ≠ []` — the register holds a `?` mark.
  -- Where no mark is held the pack's informative arm (`∀ nv ∈ markedCols sc, …`) is vacuously
  -- true, so a producer there pays the left arm for free; the arm must therefore be FALSE at
  -- unmarked pauses (not a tautology, item 424's lesson) and the marked pauses must all sit
  -- under an open `?` line.  Both pinned by input and position.
  let inputs : List String :=
    [ "a: 1", "- a\n- b", "---\na: 1\n...\n", "k:\n  - a\n  - b", "? a\n: b", "- - a\n  - b",
      "k:\n  v: w\n  x: y", "- a: 1\n  b: 2", "? - a\n: b", "a:\n- b", "k:\n- x: 1\n  y: 2",
      "? a\n? b\n: c", "k:\n  ? a\n  : b", "- ? a\n  : b", "? a: 1\n: b", "- a\n- ? b\n  : c",
      "? |\n  k\n: v", "k: v\n? a\n: b", "[a]\n? b\n: c", "? a\n- b", "? a\n  - b\n: c",
      "k:\n  ? a\n  - b", "- ? a\n  - b", "? a\n:\n- b", "? k\n: - a\n  - b" ]
  let mut pauses := 0
  let mut unmarked := 0
  let mut unmarkedLive := 0
  let mut markedRefused := 0
  let mut marked : List String := []
  -- Review on #250: the `:` STEP on a marked state — does the mark survive into the post-dispatch
  -- state (`PackAlt.step_value`'s question)?  Counted at every `:` pause whose pre-state is marked.
  let mut colonMarked := 0
  let mut colonErased := 0
  for input in inputs do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:80] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        let m := L4YAML.Proofs.RegisterWitness.markedCols sP
        if sP.flowLevel == 0 && c != '#' then
          pauses := pauses + 1
          let live := sP.explicitKeyLine.isSome
          if m.isEmpty then
            unmarked := unmarked + 1
            if live then unmarkedLive := unmarkedLive + 1
          else
            marked := marked ++ [s!"{repr input}@{sP.line}:{sP.col} marks={m}"]
            if !live then markedRefused := markedRefused + 1
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) =>
          if sP.flowLevel == 0 && c == ':' && !m.isEmpty then
            colonMarked := colonMarked + 1
            if (L4YAML.Proofs.RegisterWitness.markedCols sN).isEmpty then colonErased := colonErased + 1
          s := sN
        | _ => break
      | _ => break
  check state s!"P90 (ω-pay) `markedCols sc ≠ []` over the block pauses (item 441): unmarked={unmarked} (of which `?` line open={unmarkedLive}) marked={marked.length} (of which no `?` line open={markedRefused}) of {pauses}; `:` steps on a marked state={colonMarked}, mark erased by the step={colonErased}; marked: {marked}"
    -- Pinned by position: the marked pauses are exactly the pauses under an open `?` line (34 of
    -- 131, none without one), and no unmarked pause has a `?` line open — the projection
    -- `markedCols sc ≠ []` coincides with item 187's `explicitKeyLine ≠ none` over the block pauses.
    (pauses == 131 && unmarked == 97 && unmarkedLive == 0 && markedRefused == 0 &&
      colonMarked == 13 && colonErased == 12 &&
      marked == ["\"? a\\n: b\"@0:2 marks=[0]",
        "\"? a\\n: b\"@1:0 marks=[0]",
        "\"? - a\\n: b\"@0:2 marks=[0]",
        "\"? - a\\n: b\"@0:4 marks=[0]",
        "\"? - a\\n: b\"@1:0 marks=[0]",
        "\"? a\\n? b\\n: c\"@0:2 marks=[0]",
        "\"? a\\n? b\\n: c\"@1:2 marks=[0]",
        "\"? a\\n? b\\n: c\"@2:0 marks=[0]",
        "\"k:\\n  ? a\\n  : b\"@1:4 marks=[2]",
        "\"k:\\n  ? a\\n  : b\"@2:2 marks=[2]",
        "\"- ? a\\n  : b\"@0:4 marks=[2]",
        "\"- ? a\\n  : b\"@1:2 marks=[2]",
        "\"? a: 1\\n: b\"@0:2 marks=[0]",
        "\"? a: 1\\n: b\"@0:3 marks=[0]",
        "\"? a: 1\\n: b\"@0:5 marks=[0]",
        "\"? a: 1\\n: b\"@1:0 marks=[0]",
        "\"- a\\n- ? b\\n  : c\"@1:4 marks=[2]",
        "\"- a\\n- ? b\\n  : c\"@2:2 marks=[2]",
        "\"? |\\n  k\\n: v\"@0:2 marks=[0]",
        "\"? |\\n  k\\n: v\"@2:0 marks=[0]",
        "\"k: v\\n? a\\n: b\"@1:2 marks=[0]",
        "\"k: v\\n? a\\n: b\"@2:0 marks=[0]",
        "\"? a\\n- b\"@0:2 marks=[0]",
        "\"? a\\n- b\"@1:0 marks=[0]",
        "\"? a\\n  - b\\n: c\"@0:2 marks=[0]",
        "\"? a\\n  - b\\n: c\"@2:0 marks=[0]",
        "\"k:\\n  ? a\\n  - b\"@1:4 marks=[2]",
        "\"k:\\n  ? a\\n  - b\"@2:2 marks=[2]",
        "\"- ? a\\n  - b\"@0:4 marks=[2]",
        "\"- ? a\\n  - b\"@1:2 marks=[2]",
        "\"? a\\n:\\n- b\"@0:2 marks=[0]",
        "\"? a\\n:\\n- b\"@1:0 marks=[0]",
        "\"? k\\n: - a\\n  - b\"@0:2 marks=[0]",
        "\"? k\\n: - a\\n  - b\"@1:0 marks=[0]"])

def testPackAltNegative (state : IO.Ref TestCollector) : IO Unit := do
  -- P91 (item 444, (ω-negative)): Rule 2 on the WHOLE restated disjunction, not the arm (item 441's
  -- lesson): with `PackAlt sc := ExplicitValueRefused sc` the chain field reads
  -- `(∀ nv ∈ markedCols sc, …) ∨ sc.explicitKeyLine = none`, inhabited for FREE exactly where
  -- `markedCols sc = []` or the register is closed.  What the pauses can measure is that free
  -- domain and its complement — the marked, live pauses where only the pack's own continuation
  -- can inhabit the disjunction (whether it does is the producer's question, not the pause's);
  -- the negative must add no pause the vacuous arm does not already cover.
  let inputs : List String :=
    [ "a: 1", "- a\n- b", "---\na: 1\n...\n", "k:\n  - a\n  - b", "? a\n: b", "- - a\n  - b",
      "k:\n  v: w\n  x: y", "- a: 1\n  b: 2", "? - a\n: b", "a:\n- b", "k:\n- x: 1\n  y: 2",
      "? a\n? b\n: c", "k:\n  ? a\n  : b", "- ? a\n  : b", "? a: 1\n: b", "- a\n- ? b\n  : c",
      "? |\n  k\n: v", "k: v\n? a\n: b", "[a]\n? b\n: c", "? a\n- b", "? a\n  - b\n: c",
      "k:\n  ? a\n  - b", "- ? a\n  - b", "? a\n:\n- b", "? k\n: - a\n  - b" ]
  let mut pauses := 0
  let mut freeVacuous := 0
  let mut freeRefusedOnly := 0
  let mut markedLive := 0
  for input in inputs do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:80] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        if sP.flowLevel == 0 && c != '#' then
          pauses := pauses + 1
          let vac := (L4YAML.Proofs.RegisterWitness.markedCols sP).isEmpty
          let refused := sP.explicitKeyLine.isNone
          if vac then freeVacuous := freeVacuous + 1
          else if refused then freeRefusedOnly := freeRefusedOnly + 1
          else markedLive := markedLive + 1
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) => s := sN
        | _ => break
      | _ => break
  check state s!"P91 (ω-negative) `(∀ nv ∈ markedCols sc, …) ∨ ExplicitValueRefused sc` over the block pauses (item 444): free by the vacuous pack={freeVacuous}, free by the refusal alone={freeRefusedOnly}, marked and live (the pack's continuation the only inhabitant)={markedLive} of {pauses}"
    -- Not free everywhere: at the 34 marked pauses of P90 neither disjunct is in hand by the
    -- register alone; the refusal adds nothing the vacuous arm does not cover (refused ⇔ unmarked).
    (pauses == 131 && freeVacuous == 97 && freeRefusedOnly == 0 && markedLive == 34)

def testPackAltUnmarkedRefused (state : IO.Ref TestCollector) : IO Unit := do
  -- P92 (item 455, (ω-pay-refused)): the direction the unmarked writers spend — item 410's
  -- `RegisterWitness.refused_of_markedCols_eq_nil` read at the pauses: wherever the projection
  -- `markedCols sP` is EMPTY the register is dead (`explicitKeyLine = none`).  The lemma asks
  -- `Sound` and `flowLevel = 0`; the grid measures the block pauses (where the pay spends it) and
  -- the flow pauses separately (where the premise is missing — a flow writer may not use it).
  let inputs : List String :=
    [ "a: 1", "- a\n- b", "---\na: 1\n...\n", "k:\n  - a\n  - b", "? a\n: b", "- - a\n  - b",
      "k:\n  v: w\n  x: y", "- a: 1\n  b: 2", "? - a\n: b", "a:\n- b", "k:\n- x: 1\n  y: 2",
      "? a\n? b\n: c", "k:\n  ? a\n  : b", "- ? a\n  : b", "? a: 1\n: b", "- a\n- ? b\n  : c",
      "? |\n  k\n: v", "k: v\n? a\n: b", "[a]\n? b\n: c", "? a\n- b", "? a\n  - b\n: c",
      "k:\n  ? a\n  - b", "- ? a\n  - b", "? a\n:\n- b", "? k\n: - a\n  - b",
      "[a, b]", "{a: b}", "? [a]\n: b", "[? a : b]", "{? a : b}", "k: [a, ? b : c]", "? {a: b}\n: c",
      "- [a, {b: c}]", "? a\n: [b]", "{a: [b, c], ? d : e}" ]
  let mut blockPauses := 0
  let mut blockUnmarked := 0
  let mut blockUnmarkedLive : List String := []
  let mut flowPauses := 0
  let mut flowUnmarked := 0
  let mut flowUnmarkedLive : List String := []
  for input in inputs do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:80] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        if c != '#' then
          let vac := (L4YAML.Proofs.RegisterWitness.markedCols sP).isEmpty
          let live := sP.explicitKeyLine.isSome
          if sP.flowLevel == 0 then
            blockPauses := blockPauses + 1
            if vac then
              blockUnmarked := blockUnmarked + 1
              if live then blockUnmarkedLive := blockUnmarkedLive ++ [s!"{repr input}@{sP.line}:{sP.col}"]
          else
            flowPauses := flowPauses + 1
            if vac then
              flowUnmarked := flowUnmarked + 1
              if live then flowUnmarkedLive := flowUnmarkedLive ++ [s!"{repr input}@{sP.line}:{sP.col}"]
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) => s := sN
        | _ => break
      | _ => break
  IO.println s!"P92 block pauses={blockPauses} unmarked={blockUnmarked} unmarked-live={blockUnmarkedLive}"
  IO.println s!"P92 flow pauses={flowPauses} unmarked={flowUnmarked} unmarked-live={flowUnmarkedLive}"
  check state s!"P92 (ω-pay-refused) unmarked ⇒ refused at every BLOCK pause (item 455): {blockUnmarked} of {blockPauses} pauses unmarked, 0 of them with a live register; flow pauses {flowPauses} / unmarked {flowUnmarked} / live {flowUnmarkedLive.length} measured, not spent"
    (blockPauses > 131 && blockUnmarkedLive.isEmpty)

def testPackChainCarrier (state : IO.Ref TestCollector) : IO Unit := do
  -- P94 (item 460, (ω-carrier-read)): the chain fields `h_kslot` / `h_kslotUp` already range over
  -- EVERY mark (`MarkedColsIn`); what the pack producers must supply at the `?` dispatch that
  -- parks an entry is the pack for the whole chain.  Measured, not spent — and only the SURFACE
  -- half: a parse says the `:` is a valid continuation, not WHICH frame (`ResumeFrames` at
  -- `[FrameLevel.map nv]`) it resumes; that witness is the crossings' theorem.  (i) the non-strict
  -- guard's lemma — at every block pause every mark is ≤ the pause's own column; (ii) the park
  -- step — a block `?` at column `c` makes the marks `(before.filter (· < c)) ++ [c]`; (iii) the
  -- carrier — after the `?` entry's node completes (its lines indented past the `?`, plus a
  -- same-column `- ` when the `?` line is bare), a `:` at EVERY open mark's column parses, the
  -- depth-2/3 chains and the sequence-as-key shapes included; (iv) a flow `?` adds no mark.
  let inputs : List String :=
    [ "? a\n: b", "?\n- a\n: b", "?\n  - a\n: b", "k:\n  ?\n  - a\n  : b", "- ?\n  - a\n  : b",
      "?\n  ?\n    - a\n  : b\n: c", "?\n  ?\n    ?\n      - a\n    : b\n  : c\n: d",
      "?\n  - ?\n      - a\n    : b\n: c", "- ?\n    - a\n  : b", "?\n  k:\n    - a\n: b",
      "? a\n? b\n: c", "k:\n  ? a\n  : b", "- ? a\n  : b", "? a: 1\n: b", "- a\n- ? b\n  : c",
      "? [a, b]\n: c", "? {a: b}\n: c", "?\n  - [a, ? b : c]\n: d", "?\n  ?\n    [? a : b]\n  : c\n: d",
      "?\n  ?\n    - a\n  ? b\n: w", "? a\n- b", "k:\n  ? a\n  - b", "?\n  ?\n  - a\n  : b\n: c",
      "?\n  - ?\n    - a\n    : b\n: c", "? |\n  k\n: v", "?\n  ? a\n  : b\n  ? c\n  : d\n: e",
      "- ?\n    ?\n      ?\n        - a\n      : b\n    : c\n  : d",
      "k:\n  ?\n    ?\n      ?\n        a\n      : b\n    : c\n  : d", "?\n  - {? a : b, c: d}\n: e" ]
  let mut markedPauses := 0
  let mut boundViol : List String := []
  let mut qPauses := 0
  let mut qDeep := 0
  let mut parkExc : List String := []
  let mut contChecks := 0
  let mut rejects : List String := []
  let mut flowQ := 0
  let mut flowExc : List String := []
  for input in inputs do
    let chars := input.toList
    let lines := (input.splitOn "\n").toArray
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:80] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        let marks := L4YAML.Proofs.RegisterWitness.markedCols sP
        let isQ := c == '?' && (chars[sP.offset + 1]?.map (fun ch => ch == ' ' || ch == '\n')).getD true
        if c != '#' && sP.flowLevel == 0 && !marks.isEmpty then
          markedPauses := markedPauses + 1
          for nv in marks do
            if nv > sP.col then
              boundViol := boundViol ++ [s!"{repr input}@{sP.line}:{sP.col} nv={nv}"]
        let after := match L4YAML.Scanner.scanNextToken s with
          | .ok (some sN) => some (L4YAML.Proofs.RegisterWitness.markedCols sN)
          | _ => none
        if isQ && sP.flowLevel == 0 then
          qPauses := qPauses + 1
          if marks.length ≥ 2 then qDeep := qDeep + 1
          let expected := marks.filter (· < sP.col) ++ [sP.col]
          if after != some expected then
            parkExc := parkExc ++ [s!"{repr input}@{sP.line}:{sP.col} before={marks} after={after}"]
          let qLine := lines[sP.line]?.getD ""
          let bare := (qLine.toList.drop (sP.col + 1)).all (· == ' ')
          let indentOf (l : String) : Nat := (l.toList.takeWhile (· == ' ')).length
          let mut last := sP.line
          for i in [sP.line + 1 : lines.size] do
            let l := lines[i]!
            let blank := l.toList.all (· == ' ')
            let inNode := blank || indentOf l > sP.col ||
              (bare && indentOf l == sP.col && (l.toList.drop sP.col).take 2 == ['-', ' '])
            if i == last + 1 && inNode then last := i
          let pre := "\n".intercalate ((lines.toList.take (last + 1)))
          for nv in (after.getD expected) do
            contChecks := contChecks + 1
            let cont := pre ++ "\n" ++ String.ofList (List.replicate nv ' ') ++ ": v\n"
            match L4YAML.TokenParser.parseYaml cont with
            | .ok _ => pure ()
            | .error _ => rejects := rejects ++ [s!"{repr input}@{sP.line}:{sP.col} nv={nv}"]
        if isQ && sP.flowLevel > 0 then
          flowQ := flowQ + 1
          if after != some marks then
            flowExc := flowExc ++ [s!"{repr input}@{sP.line}:{sP.col} before={marks} after={after}"]
        match after with
        | some _ =>
          match L4YAML.Scanner.scanNextToken s with
          | .ok (some sN) => s := sN
          | _ => break
        | none => break
      | _ => break
  IO.println s!"P94 marked block pauses={markedPauses} bound-violations={boundViol} `?` pauses={qPauses} deep={qDeep} park-exceptions={parkExc} continuation checks={contChecks} rejects={rejects} flow `?`={flowQ} flow-exceptions={flowExc}"
  check state s!"P94 (ω-carrier-read) the chain carrier at the `?` dispatch (item 460): {markedPauses} marked block pauses, a mark right of the pause column at {boundViol.length}; {qPauses} block `?` pauses ({qDeep} at chain depth ≥ 2), the park step off by {parkExc.length}; the node-completed `:` continuation (the carrier's surface, not its frame witness) parses at every open mark except {rejects}; {flowQ} flow `?` pauses add a mark at {flowExc.length}"
    (markedPauses ≥ 60 && boundViol.isEmpty && qPauses ≥ 25 && qDeep ≥ 3 && parkExc.isEmpty &&
      contChecks ≥ 40 && rejects.isEmpty && flowQ ≥ 3 && flowExc.isEmpty)

def testPackBirthsOnDrop (state : IO.Ref TestCollector) : IO Unit := do
  -- P93 (item 457, (ω-births)): the three `on-drop` producers' 21 `PackAlt` writes
  -- (`accum_block_on_closeThenBlock` 13 / `_pendingBlockContent` 4 / `_pendingBlock` 4), read by
  -- class at the scanner's block pauses.  (A) the level guards at the `-` pause's own column `k`:
  -- the non-strict `nv ≤ k` (closeThenBlock's `-` landings) fails at a mark DEEPER than the
  -- landing; a mark AT the `-`'s column (`? a⏎- b`, `?⏎- a`) is counted too — item 462 read the
  -- STRICT `nv + 1 ≤ k` guards into the `:`/`?` opener arm, so that count is a `-` landing fact
  -- (the keyed-sibling / sequence-as-key shapes), not a strict-guard domain.  (B)/(C) the
  -- chain classes — at a `-` pause, how many frames up do the marks sit (one: the carried
  -- `h_kslotUp` / `nsU` chain; two or more: no carrier)?  And the pack's own continuation — at
  -- every marked pause and every mark `nv`, with the pause's line KEPT (the landing consumed), does
  -- a `:` at column `nv` on the next line still parse?  Measured, not spent: the pay waits on the
  -- library.
  let inputs : List String :=
    [ "a: 1", "- a\n- b", "k:\n  - a\n  - b", "? a\n: b", "- - a\n  - b",
      "k:\n  v: w\n  x: y", "- a: 1\n  b: 2", "? - a\n: b", "a:\n- b", "k:\n- x: 1\n  y: 2",
      "? a\n? b\n: c", "k:\n  ? a\n  : b", "- ? a\n  : b", "? a: 1\n: b", "- a\n- ? b\n  : c",
      "? |\n  k\n: v", "k: v\n? a\n: b", "[a]\n? b\n: c", "? a\n- b", "? a\n  - b\n: c",
      "k:\n  ? a\n  - b", "- ? a\n  - b", "? a\n:\n- b", "? k\n: - a\n  - b", "? [a]\n: b",
      "? {a: b}\n: c", "? a\n: [b]",
      "?\n  - a\n: b", "?\n  ?\n    - a\n  : b\n: c", "- ?\n    - a\n  : b", "k:\n  ?\n    - a\n  : b",
      "?\n  ?\n    ?\n      - a\n    : b\n  : c\n: d", "? - a\n  - b\n: c", "?\n  k:\n    - a\n: b",
      "?\n  - a\n  - b\n: c", "- ?\n  - a\n  : b", "?\n  - ?\n      - a\n    : b\n: c",
      "?\n- a\n: b", "k:\n  ?\n  - a\n  : b" ]
  let mut markedPauses := 0
  let mut guardViol : List String := []
  let mut strictFail : List String := []
  let mut dashPauses := 0
  let mut depth0 := 0
  let mut depth1 := 0
  let mut depth1Map := 0
  let mut depth2 := 0
  let mut depth2Ex : List String := []
  let mut contChecks := 0
  let mut rejects : List String := []
  for input in inputs do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:80] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        if c != '#' && sP.flowLevel == 0 then
          let marks := L4YAML.Proofs.RegisterWitness.markedCols sP
          if !marks.isEmpty then
            markedPauses := markedPauses + 1
            let top : Int := (sP.indents.back?.map (·.column)).getD (-1)
            let chars := input.toList
            let lineEnd := sP.offset + (chars.drop sP.offset |>.takeWhile (· != '\n')).length
            for nv in marks do
              if (nv : Int) > top then
                guardViol := guardViol ++ [s!"{repr input}@{sP.line}:{sP.col} nv={nv} top={top}"]
              contChecks := contChecks + 1
              let pre := String.ofList (chars.take lineEnd) ++ "\n"
              let cont := pre ++ String.ofList (List.replicate nv ' ') ++ ": v\n"
              match L4YAML.TokenParser.parseYaml cont with
              | .ok _ => pure ()
              | .error _ => rejects := rejects ++ [s!"{repr input}@{sP.line}:{sP.col} nv={nv}"]
            if c == '-' then
              dashPauses := dashPauses + 1
              for nv in marks do
                if nv > sP.col then
                  guardViol := guardViol ++ [s!"{repr input}@{sP.line}:{sP.col} nv={nv} k={sP.col}"]
                if nv == sP.col then
                  strictFail := strictFail ++ [s!"{repr input}@{sP.line}:{sP.col} nv={nv}"]
                let above := (sP.indents.toList.filter (fun e => e.column > (nv : Int))).length
                if above == 0 then depth0 := depth0 + 1
                else if above == 1 then
                  depth1 := depth1 + 1
                  if (sP.indents.toList.find? (fun e => e.column == (nv : Int))).map (·.isSequence)
                      == some false then
                    depth1Map := depth1Map + 1
                else
                  depth2 := depth2 + 1
                  depth2Ex := depth2Ex ++ [s!"{repr input}@{sP.line}:{sP.col} nv={nv}"]
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) => s := sN
        | _ => break
      | _ => break
  IO.println s!"P93 marked block pauses={markedPauses} guard-violations={guardViol} strict-fail={strictFail} dash pauses={dashPauses} depth0={depth0} depth1={depth1} (map {depth1Map}) depth2+={depth2} {depth2Ex} continuation checks={contChecks} rejects={rejects}"
  check state s!"P93 (ω-births) the on-drop classes at the block pauses (item 457): {markedPauses} marked pauses, a mark deeper than the landing / the stack top at {guardViol.length} (the non-strict guards' failure set empty), a mark AT the `-` landing column at {strictFail.length} (the keyed-sibling / sequence-as-key shapes; item 462: the strict guards are the `:`/`?` arm's, not the `-`'s), `-` pauses {dashPauses} with marks at depth 0 / 1 / 2+ = {depth0} / {depth1} / {depth2} (depth 1 all mapping frames: {depth1Map}), the `:` continuation after the pause's line parses except at {rejects}"
    (markedPauses ≥ 40 && guardViol.isEmpty && depth1 ≥ 5 && depth1Map == depth1 &&
      strictFail == ["\"? a\\n- b\"@1:0 nv=0", "\"k:\\n  ? a\\n  - b\"@2:2 nv=2",
        "\"- ? a\\n  - b\"@1:2 nv=2", "\"- ?\\n  - a\\n  : b\"@1:2 nv=2",
        "\"?\\n- a\\n: b\"@1:0 nv=0", "\"k:\\n  ?\\n  - a\\n  : b\"@2:2 nv=2"] &&
      rejects == ["\"? a\\n- b\"@1:0 nv=0", "\"k:\\n  ? a\\n  - b\"@2:2 nv=2",
        "\"- ? a\\n  - b\"@1:2 nv=2"] &&
      depth2Ex == ["\"?\\n  ?\\n    ?\\n      - a\\n    : b\\n  : c\\n: d\"@3:6 nv=0",
        "\"?\\n  - ?\\n      - a\\n    : b\\n: c\"@2:6 nv=0"])

def testPackStrictGuardLane (state : IO.Ref TestCollector) : IO Unit := do
  -- P95 (item 462, (ω-pay-births) step (b)): the four STRICT guards `nv + 1 ≤ k` / `n + 1 ≤ k`
  -- (`accum_block_on_closeThenBlock` L28648 / L28678, `accum_block_on_pendingBlock` L30649 /
  -- L30690) sit in the `:` / `?` OPENER arm (`indicator_open_map`), not at a `-` landing: `k` is
  -- the `:`/`?`'s column, `n` the park's own mark.  Read at the scanner, for every block `:`/`?`
  -- pause on a marked state: (i) the lane — `k > n` (nested), `k = n` (the park's own `:` or a
  -- sibling `?`), `k < n` (a dedent to an enclosing mark); (ii) the step — the marks after the
  -- token are `before.filter (· < k)` (+ `[k]` for a `?`): the park's own mark is consumed or
  -- closed, never carried; (iii) the ancestors' surface — after the landing's WHOLE entry (its
  -- node, and for a `?` its own `:` value line at `k`) completes, a `:` at every surviving mark's
  -- column parses; (iv) how many `k ≤ n` pauses have NO ancestor — the park's own mark's pack is
  -- still owed there (`MarkedColsIn sc ns` holds every mark of `sc`).  Measured, not spent.
  let inputs : List String :=
    [ "? a\n: b", "?\n- a\n: b", "?\n  - a\n: b", "k:\n  ?\n  - a\n  : b", "- ?\n  - a\n  : b",
      "?\n  ?\n    - a\n  : b\n: c", "?\n  ?\n    ?\n      - a\n    : b\n  : c\n: d",
      "?\n  - ?\n      - a\n    : b\n: c", "- ?\n    - a\n  : b", "?\n  k:\n    - a\n: b",
      "? a\n? b\n: c", "k:\n  ? a\n  : b", "- ? a\n  : b", "? a: 1\n: b", "- a\n- ? b\n  : c",
      "? [a, b]\n: c", "? {a: b}\n: c", "?\n  - [a, ? b : c]\n: d", "?\n  ?\n    [? a : b]\n  : c\n: d",
      "?\n  ?\n    - a\n  ? b\n: w", "?\n  ?\n  - a\n  : b\n: c", "? |\n  k\n: v",
      "?\n  ? a\n  : b\n  ? c\n  : d\n: e", "- ?\n    ?\n      ?\n        - a\n      : b\n    : c\n  : d",
      "k:\n  ?\n    ?\n      ?\n        a\n      : b\n    : c\n  : d", "?\n  ? a\n: b",
      "?\n  ?\n    ? a\n: b", "?\n  ? a\n  ? b\n: c", "?\n  ?\n    - a\n: b", "? a\n:\n  ? b\n  : c" ]
  let mut pauses := 0
  let mut nested := 0
  let mut own := 0
  let mut dedent := 0
  let mut stepExc : List String := []
  let mut noAnc := 0
  let mut ancChecks := 0
  let mut rejects : List String := []
  for input in inputs do
    let chars := input.toList
    let lines := (input.splitOn "\n").toArray
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:80] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        let before := L4YAML.Proofs.RegisterWitness.markedCols s
        let isInd := (c == ':' || c == '?') &&
          (chars[sP.offset + 1]?.map (fun ch => ch == ' ' || ch == '\n')).getD true
        let after := match L4YAML.Scanner.scanNextToken s with
          | .ok (some sN) => some (L4YAML.Proofs.RegisterWitness.markedCols sN)
          | _ => none
        if isInd && sP.flowLevel == 0 && !before.isEmpty then
          pauses := pauses + 1
          let n := before.foldl max 0
          let k := sP.col
          if k > n then nested := nested + 1
          else if k == n then own := own + 1
          else dedent := dedent + 1
          let surv := before.filter (· < k)
          let expected := surv ++ (if c == '?' then [k] else [])
          if after != some expected then
            stepExc := stepExc ++ [s!"{repr input}@{sP.line}:{k} c={c} before={before} after={after}"]
          if k ≤ n && surv.isEmpty then noAnc := noAnc + 1
          let indentOf (l : String) : Nat := (l.toList.takeWhile (· == ' ')).length
          let mut last := sP.line
          for i in [sP.line + 1 : lines.size] do
            let l := lines[i]!
            let blank := l.toList.all (· == ' ')
            let valueLine := c == '?' && indentOf l == k &&
              (l.toList.drop k).head? == some ':' &&
              ((l.toList.drop (k + 1)).head?.map (· == ' ')).getD true
            if i == last + 1 && (blank || indentOf l > k || valueLine) then last := i
          let pre := "\n".intercalate (lines.toList.take (last + 1))
          for nv in surv do
            ancChecks := ancChecks + 1
            let cont := pre ++ "\n" ++ String.ofList (List.replicate nv ' ') ++ ": v\n"
            match L4YAML.TokenParser.parseYaml cont with
            | .ok _ => pure ()
            | .error _ => rejects := rejects ++ [s!"{repr input}@{sP.line}:{k} c={c} nv={nv}"]
        match after with
        | some _ =>
          match L4YAML.Scanner.scanNextToken s with
          | .ok (some sN) => s := sN
          | _ => break
        | none => break
      | _ => break
  IO.println s!"P95 marked `:`/`?` pauses={pauses} nested={nested} own={own} dedent={dedent} step-exceptions={stepExc} no-ancestor k≤n={noAnc} ancestor checks={ancChecks} rejects={rejects}"
  check state s!"P95 (ω-pay-births) the strict guards' lane at the `:`/`?` landings (item 462): {pauses} marked pauses — k > n {nested} / k = n {own} / k < n {dedent}; the step (marks after = survivors below k, + the `?`'s own) off at {stepExc.length}; {noAnc} of the k ≤ n pauses have no ancestor (the park's own mark's pack still owed there); the ancestors' `:` continuation after the whole entry parses at every survivor except {rejects}"
    (pauses ≥ 30 && nested ≥ 5 && own ≥ 15 && dedent ≥ 3 && stepExc.isEmpty && noAnc ≥ 10 &&
      ancChecks ≥ 10 && rejects.isEmpty)

def testSeqTopRefusedArm (state : IO.Ref TestCollector) : IO Unit := do
  -- P89 (item 438, (χ-seqtop-refused)): the negative arm `ExplicitValueRefused s ∨ SeqTopKey s`
  -- proposed for `content_dispatch_routed`'s `h_resF` premise must NOT be a tautology over the
  -- block pauses (item 424's lesson: `Refused ∨ Armed` was inhabited everywhere).  Both disjuncts
  -- fail exactly where an explicit `?` key line is open and the stack top is not a sequence level
  -- at the simple key's column; those pauses are pinned by input and position.
  let inputs : List String :=
    [ "a: 1", "- a\n- b", "---\na: 1\n...\n", "k:\n  - a\n  - b", "? a\n: b", "- - a\n  - b",
      "k:\n  v: w\n  x: y", "- a: 1\n  b: 2", "? - a\n: b", "a:\n- b", "k:\n- x: 1\n  y: 2",
      "? a\n? b\n: c", "k:\n  ? a\n  : b", "- ? a\n  : b", "? a: 1\n: b", "- a\n- ? b\n  : c",
      "? |\n  k\n: v", "k: v\n? a\n: b", "[a]\n? b\n: c" ]
  let mut pauses := 0
  let mut refused := 0
  let mut seqTopKey := 0
  let mut bothFail : List String := []
  let mut col0Pauses := 0
  let mut col0Refused := 0
  for input in inputs do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:80] do
      match L4YAML.Scanner.scanNextToken_preprocess s with
      | .ok (some (sP, c)) =>
        if sP.flowLevel == 0 && c != '#' then
          pauses := pauses + 1
          let r := sP.explicitKeyLine.isNone
          let q := (sP.indents.back?.map fun e =>
            e.isSequence && e.column == (sP.simpleKey.pos.col : Int)) == some true
          if r then refused := refused + 1
          if q then seqTopKey := seqTopKey + 1
          if !r && !q then bothFail := bothFail ++ [s!"{repr input}@{sP.line}:{sP.col}"]
          if sP.col == 0 then
            col0Pauses := col0Pauses + 1
            if r then col0Refused := col0Refused + 1
        match L4YAML.Scanner.scanNextToken s with
        | .ok (some sN) => s := sN
        | _ => break
      | _ => break
  check state s!"P89 (χ-seqtop-refused) `ExplicitValueRefused ∨ SeqTopKey` over the block pauses (item 438): refused={refused} seqTopKey={seqTopKey} of {pauses}; both fail at {bothFail.length}: {bothFail}; column-0 pauses refused={col0Refused}/{col0Pauses}"
    -- Pinned by position (review on #240: pin which pauses, not how many): every both-fail pause
    -- sits on an explicit `?` key line; the two disjuncts are disjoint from it, not a tautology.
    (pauses == 103 && refused == 81 && seqTopKey == 4 && col0Refused == 28 && col0Pauses == 34 &&
      bothFail == ["\"? a\\n: b\"@0:2",
        "\"? a\\n: b\"@1:0",
        "\"? - a\\n: b\"@0:2",
        "\"? - a\\n: b\"@0:4",
        "\"? - a\\n: b\"@1:0",
        "\"? a\\n? b\\n: c\"@0:2",
        "\"? a\\n? b\\n: c\"@1:2",
        "\"? a\\n? b\\n: c\"@2:0",
        "\"k:\\n  ? a\\n  : b\"@1:4",
        "\"k:\\n  ? a\\n  : b\"@2:2",
        "\"- ? a\\n  : b\"@0:4",
        "\"- ? a\\n  : b\"@1:2",
        "\"? a: 1\\n: b\"@0:2",
        "\"? a: 1\\n: b\"@0:3",
        "\"? a: 1\\n: b\"@0:5",
        "\"? a: 1\\n: b\"@1:0",
        "\"- a\\n- ? b\\n  : c\"@1:4",
        "\"- a\\n- ? b\\n  : c\"@2:2",
        "\"? |\\n  k\\n: v\"@0:2",
        "\"? |\\n  k\\n: v\"@2:0",
        "\"k: v\\n? a\\n: b\"@1:2",
        "\"k: v\\n? a\\n: b\"@2:0"])

def testFlowCarrier (state : IO.Ref TestCollector) : IO Unit := do
  let nestedQ : List String := ["?\n  ? -\n: w\n", "? - ? - a\n  : b\n: c\n", "?\n  ?\n    -\n    - b\n  ? c\n: w\n", "? ? - a\n  : b\n: c\n", "- ? - a\n  : b\n"]
  let singleQ : List String := ["? - a\n: b\n", "?\n  - a\n  - b\n: w\n", "k:\n  ? - a\n  : b\n", "? -\n: w\n"]
  -- 70 (item 406, PRICED) — the flow-open KEY FACE's chain (`FlowBaseRoutes.key`) is FABRICATED at
  -- `flowKeyRoute_of_root` (`⟨[nv], …⟩` once, `⟨[], …⟩` four times).  Domaining it
  -- (`flip_kslot_domain.py --round2`, now `scripts/flips/item397_kslot_domain_round2.json`) would owe `MarkedColsIn s0 []` / `[nv]` — so read which
  -- block-context flow opens stand under marks (the fabrication is honest only at `markless`).
  let flowOpens : List String :=
    [ "[a]: b", "{a: 1}: b", "[1]\n[2]: b", "? [a]: b", "? [a]\n: b", "? - [1]\n: w",
      "?\n  ? [x]: y\n  : z\n: w", "? {a: 1}: b\n: c", "- ? [a]: b", "k:\n  ? [a]: b\n  : c",
      "? [a, b]: c\n? [d]: e", "?\n  [a]: b\n: c" ]
  let mut opens := 0
  let mut openMarked := 0
  let mut openTwo := 0
  let mut openBare := 0
  for input in flowOpens do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken s with
      | .ok (some sN) =>
        match L4YAML.Scanner.scanNextToken_preprocess s with
        | .ok (some (sP, c)) =>
          if (c == '[' || c == '{') && !sP.inFlow then
            opens := opens + 1
            let mc := L4YAML.Proofs.RegisterWitness.markedCols sN
            if mc.isEmpty then openBare := openBare + 1 else openMarked := openMarked + 1
            if mc.length ≥ 2 then openTwo := openTwo + 1
        | _ => pure ()
        s := sN
      | _ => break
  check state s!"P70 flow-open key face domain (item 406): block-context flow opens={opens} under marks={openMarked} (two or more={openTwo}) markless={openBare}"
    (opens > 0 && openMarked > 0 && openTwo > 0 && openBare > 0)

  -- 71 (item 407, the flow carrier's pendingKeys conjunct, read BEFORE the proof) — from the state a
  -- block-context `[` / `{` dispatch produces to every accepted pause while the flow is open,
  -- `pendingKeys` is the open's (predicted: 0 violations); negative control: a block interior
  -- (a `?` or `-` dispatch) does change it at some pause (predicted: > 0).
  let flowBodies : List String :=
    [ "[a]: b", "{a: 1}: b", "[a, [b, c], {d: e}]: f", "? [a,\n  b]: c", "? - [1, {x: y}]\n: w",
      "k: [a, b]\nq: c", "[\n  a,\n  b\n]: c", "{a: [1, 2], b: {c: d}}", "? {a: 1}: b\n: c",
      "- [a]\n- {b: c}", "k:\n  ? [a]: b\n  : c", "&x [a, *x]" ]
  let mut flowPauses := 0
  let mut flowBad := 0
  let mut blockChanged := 0
  for input in flowBodies ++ nestedQ ++ singleQ do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    let mut openPk : Option (Array (Option Nat)) := none
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken s with
      | .ok (some sN) =>
        match openPk with
        | some pk =>
          if sN.flowLevel > 0 then
            flowPauses := flowPauses + 1
            if sN.pendingKeys != pk then flowBad := flowBad + 1
          else openPk := none
        | none =>
          if sN.flowLevel > 0 then openPk := some sN.pendingKeys
          else if sN.pendingKeys != s.pendingKeys then blockChanged := blockChanged + 1
        s := sN
      | _ => break
  check state s!"P71 flow carrier pendingKeys (item 407): flow-interior pauses={flowPauses} pendingKeys ≠ open's={flowBad}; block pauses that changed pendingKeys={blockChanged}"
    (flowPauses > 0 && flowBad == 0 && blockChanged > 0)

  -- 71 (ii) — `preprocess_pendingKeys_of_inFlow` as a STATEMENT (review flag): at every in-flow state,
  -- `scanNextToken_preprocess` itself is called and its `pendingKeys` compared, INCLUDING states whose
  -- subsequent dispatch fails (`[a: ]]`, `[ , ]`, `{a}` …), which the walk above never reaches.
  let flowBroken : List String :=
    [ "[a: ]]", "[ , ]", "{a}", "[a, b", "{a: 1,, b: 2}", "? [a: b]]\n: c", "[&x a, *y]", "{a: [1, 2}" ]
  let mut preN := 0
  let mut preBad := 0
  let mut preOnly := 0
  for input in flowBodies ++ flowBroken ++ nestedQ do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:64] do
      if s.flowLevel > 0 then
        match L4YAML.Scanner.scanNextToken_preprocess s with
        | .ok (some (sP, _)) =>
          preN := preN + 1
          if sP.pendingKeys != s.pendingKeys then preBad := preBad + 1
          match L4YAML.Scanner.scanNextToken s with
          | .ok (some _) => pure ()
          | _ => preOnly := preOnly + 1
        | _ => pure ()
      match L4YAML.Scanner.scanNextToken s with
      | .ok (some sN) => s := sN
      | _ => break
  check state s!"P71 (ii) preprocess_pendingKeys_of_inFlow direct: in-flow preprocess results={preN} pendingKeys changed={preBad}; preprocess-only states (dispatch then fails)={preOnly}"
    (preN > 0 && preBad == 0 && preOnly > 0)

  -- 72 (item 408, before the proof) — the flow key face on the PROJECTION: `markedCols` at the flow
  -- OPEN equals `markedCols` at every accepted pause while the flow is open, incl. the CLOSE
  -- (`markedCols_congr` over 407's `pendingKeys` conjunct and `h_ind_park`): predicted 0 violations.
  let mut mcPauses := 0
  let mut mcBad := 0
  let mut mcCloses := 0
  for input in flowBodies ++ nestedQ ++ singleQ do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    let mut openMc : Option (List Nat) := none
    for _ in [:64] do
      match L4YAML.Scanner.scanNextToken s with
      | .ok (some sN) =>
        match openMc with
        | some mc =>
          if sN.flowLevel > 0 then
            mcPauses := mcPauses + 1
            if L4YAML.Proofs.RegisterWitness.markedCols sN != mc then mcBad := mcBad + 1
          else
            mcCloses := mcCloses + 1
            if L4YAML.Proofs.RegisterWitness.markedCols sN != mc then mcBad := mcBad + 1
            openMc := none
        | none =>
          if sN.flowLevel > 0 then openMc := some (L4YAML.Proofs.RegisterWitness.markedCols sN)
        s := sN
      | _ => break
  check state s!"P72 flow key face projection (item 408): in-flow pauses={mcPauses} closes={mcCloses} markedCols ≠ open's={mcBad}"
    (mcPauses > 0 && mcCloses > 0 && mcBad == 0)


  -- 72 (ii) — `markedCols_congr` as a STATEMENT (review): arbitrary state PAIRS under its two hypotheses
  -- (`pendingKeys` equal, `indents` equal) with every OTHER field free to differ — empty, singleton and
  -- nested marked slots, block and flow states alike — must project the same chain; and a negative
  -- control: pairs whose `pendingKeys` or `indents` DIFFER must be able to project different chains.
  let mut cgPairs := 0
  let mut cgEmpty := 0
  let mut cgMulti := 0
  let mut cgBad := 0
  let mut cgNeg := 0
  let mut cgNegDiff := 0
  let mut prev : Option L4YAML.Scanner.ScannerState := none
  for input in flowBodies ++ nestedQ ++ singleQ ++ ["", "a", "? a\n? b\n: c", "- ? a\n  : b"] do
    let mut s := L4YAML.Scanner.ScannerState.mk' input
    for _ in [:64] do
      -- the pair: `s` and `s` with unrelated fields moved (both hypotheses hold by construction)
      let s2 : L4YAML.Scanner.ScannerState :=
        { s with allowDirectives := !s.allowDirectives, flowLevel := s.flowLevel + 3,
                 documentEverStarted := !s.documentEverStarted }
      if s2.pendingKeys == s.pendingKeys && s2.indentColumns == s.indentColumns then
        cgPairs := cgPairs + 1
        let mc := L4YAML.Proofs.RegisterWitness.markedCols s
        if mc.isEmpty then cgEmpty := cgEmpty + 1
        if mc.length ≥ 2 then cgMulti := cgMulti + 1
        if L4YAML.Proofs.RegisterWitness.markedCols s2 != mc then cgBad := cgBad + 1
      -- negative control: consecutive pauses whose `pendingKeys` or `indents` differ
      match prev with
      | some p =>
        if p.pendingKeys != s.pendingKeys || p.indentColumns != s.indentColumns then
          cgNeg := cgNeg + 1
          if L4YAML.Proofs.RegisterWitness.markedCols p != L4YAML.Proofs.RegisterWitness.markedCols s then
            cgNegDiff := cgNegDiff + 1
      | none => pure ()
      prev := some s
      match L4YAML.Scanner.scanNextToken s with
      | .ok (some sN) => s := sN
      | _ => break
  check state s!"P72 (ii) markedCols_congr direct: pairs={cgPairs} (empty={cgEmpty} two-or-more={cgMulti}) projections differ={cgBad}; negative pairs={cgNeg} of which chains differ={cgNegDiff}"
    (cgPairs > 0 && cgEmpty > 0 && cgMulti > 0 && cgBad == 0 && cgNeg > 0 && cgNegDiff > 0)

/-! **Priority 87 — S3 obligation (b) `DirectivesClosed` on `scanFiltered` output, instantiated BEFORE
    the proof (Rule 2).**  The claim: in `scanFiltered input = .ok ts` every `%YAML`/`%TAG` token is
    followed by another directive token or `.documentStart`.  The grid walks the directive run's
    every exit — `---` (closes), a second directive (continues), `...`/EOF/every content dispatch
    path (`-`, `?`, `:`, `[`, `{`, `"`, `'`, `&`, `*`, `!`, `|`, plain) which must REFUSE with
    `directiveWithoutDocument` — plus the re-arming boundary (`...` re-allows directives, `---`
    and content do not: `directiveAfterContent`), reserved `%FOO` directives (flag up, no token),
    comments/blank lines/BOM before the run, and the degenerate inputs (empty, `---`, `...`, one
    scalar) where the claim holds vacuously.  The verdict column is the prediction; on success the
    RAW `scan` fold `dirRun false … = some false` (the proof's invariant) and the filtered
    `DirectivesClosed` shape are both checked. -/
def testDirectivesClosedScan (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 87: S3 (b) DirectivesClosed — every directive run exits into `---` or another directive, or the scan is refused"
  let isDir : YamlToken → Bool
    | .versionDirective .. | .tagDirective .. => true
    | _ => false
  let closedB (vs : List YamlToken) : Bool :=
    (List.range vs.length).all fun i =>
      match vs[i]?, vs[i+1]? with
      | some t, nxt =>
        if isDir t then (match nxt with | some n => isDir n || n == .documentStart | none => false)
        else true
      | none, _ => true
  -- (input, scans?, number of directive tokens expected when it scans)
  let rows : List (String × Bool × Nat) :=
    [ ("%YAML 1.2\n---\na", true, 1), ("%TAG !e! tag:x,2000:\n---\n!e!a b", true, 1),
      ("%YAML 1.2\n%TAG !e! tag:x,2000:\n---\na", true, 2),
      ("%TAG !e! tag:x,2000:\n%YAML 1.2\n---\na", true, 2),
      ("%YAML 1.2\n---", true, 1), ("%YAML 1.2\n# c\n\n---\na", true, 1),
      ("\uFEFF%YAML 1.2\n---\na", true, 1), ("%FOO bar\n---\na", true, 0),
      ("--- a\n...\n%YAML 1.2\n---\nb", true, 1), ("a\n...\n%TAG !e! tag:x,2000:\n---\n!e!b c", true, 1),
      ("", true, 0), ("---", true, 0), ("...", true, 0), ("a", true, 0), ("--- a\n--- b", true, 0),
      -- the run exits into content, `...`, or EOF: refused
      ("%YAML 1.2\na", false, 0), ("%YAML 1.2\n...\n", false, 0), ("%YAML 1.2\n", false, 0),
      ("%YAML 1.2", false, 0), ("%FOO bar\na", false, 0), ("%FOO bar\n", false, 0),
      ("%YAML 1.2\n- a", false, 0), ("%YAML 1.2\n? a\n: b", false, 0), ("%YAML 1.2\n: a", false, 0),
      ("%YAML 1.2\n[a]", false, 0), ("%YAML 1.2\n{a: b}", false, 0), ("%YAML 1.2\n\"a\"", false, 0),
      ("%YAML 1.2\n'a'", false, 0), ("%YAML 1.2\n&x a", false, 0), ("%YAML 1.2\n*x", false, 0),
      ("%YAML 1.2\n!t a", false, 0), ("%YAML 1.2\n|\n a", false, 0), ("%YAML 1.2\n>\n a", false, 0),
      ("%TAG !e! tag:x,2000:\na: b", false, 0),
      -- directives where they are not allowed: after `---` or content without a `...`
      ("---\n%YAML 1.2\n---\na", false, 0), ("a\n---\n%YAML 1.2\n---\nb", false, 0),
      ("%YAML 1.2\n--- a\n%TAG !e! tag:x,2000:\n---\nb", false, 0),
      -- a `%` line INSIDE a plain scalar is scalar text, not a directive: scans, no directive token
      ("a\n%YAML 1.2\n---\nb", true, 0) ]
  let mut scanned := 0
  let mut refused := 0
  let mut parsed := 0
  let mut parserRejected := 0
  for (input, expOk, nDir) in rows do
    match Scanner.scanFiltered input with
    | .error e =>
      refused := refused + 1
      checkM state s!"P87 {repr input}: refused" (!expOk) s!"{repr e}"
      -- a run that opens the stream is refused for the directive reason, not something else (after
      -- content the `%` line is read as scalar text, and the refusal is whatever that text earns)
      if !expOk && (input.startsWith "%" || input.startsWith "\uFEFF%")
          && !(input.splitOn "\n").any (·.startsWith "--- ") then
        let directiveReason := match e with
          | .directiveWithoutDocument _ => true | .directiveAfterContent _ => true | _ => false
        checkM state s!"P87 {repr input}: refused on the directive" directiveReason s!"{repr e}"
    | .ok ts =>
      scanned := scanned + 1
      let vs := ts.toList.map (·.val)
      checkM state s!"P87 {repr input}: scans" expOk s!"{ts.size} tokens"
      checkM state s!"P87 {repr input}: DirectivesClosed on the filtered tokens" (closedB vs) s!"{repr vs}"
      checkM state s!"P87 {repr input}: {nDir} directive token(s)" ((vs.filter isDir).length == nDir)
        s!"got {(vs.filter isDir).length}"
      match Scanner.scan input with
      | .ok raw =>
        let rawVals := L4YAML.Proofs.DirectiveRuns.toks raw
        checkM state s!"P87 {repr input}: raw fold `dirRun false … = some false`"
          (L4YAML.Proofs.DirectiveRuns.dirRun false rawVals == some false) s!"{repr rawVals}"
        checkM state s!"P87 {repr input}: filtering placeholders is the proof's bridge"
          (L4YAML.Proofs.DirectiveRuns.toks (raw.filter fun t => t.val != .placeholder) == vs) ""
      | .error e => checkM state s!"P87 {repr input}: raw scan agrees with scanFiltered" false s!"{repr e}"
      -- the composed lemma on the same tokens: its TagUsesShaped premise, the parser verdict, and a
      -- checkFrom witness k; the full array (k = ts.size) is the one the lemma's first disjunct names
      let (pOk, cfFull) := s5TokVerdict ts
      checkM state s!"P87 {repr input}: TagUsesShaped premise holds on scanner output" (s5TagUsesShaped ts)
        s!"{repr vs}"
      if pOk then
        parsed := parsed + 1
        let ks := (List.range (ts.size + 1)).filter fun k =>
          L4YAML.Proofs.Serialization.SerializationWellFormed.checkFrom {}
            (L4YAML.Proofs.Serialization.TokenEvents.tokenEvents (ts.extract 0 k))
        checkM state s!"P87 {repr input}: parser ok ⇒ checkFrom accepts the full array (k = ts.size)" cfFull
          s!"accepted prefixes k = {ks}"
        checkM state s!"P87 {repr input}: the witness k = ts.size is among the accepted prefixes"
          (ks.contains ts.size) s!"ks = {ks} size = {ts.size}"
      else
        parserRejected := parserRejected + 1
  checkM state s!"P87 grid: scanned={scanned} refused={refused} parsed={parsed} parserRejected={parserRejected}"
    (scanned == 16 && refused == 22 && parsed == 16 && parserRejected == 0) ""

/-! **Priority 88 — S3 obligation (c) `streamEnd`-last on `scanFiltered` output, instantiated BEFORE the
    proof (Rule 2).**  The claim: `scanFiltered input = .ok ts → 0 < ts.size ∧ tok ts (ts.size - 1) =
    some .streamEnd`.  The grid walks the stream's every ending — empty input, BOM only, comments and
    blank lines only, a lone `---` or `...`, trailing newlines after `...`, documents ending in a block
    scalar / flow collection / nested mapping / directive run, a second document, inputs the scanner
    refuses (no claim) — and on every scan checks the filtered shape, the raw `scan` shape the proof
    goes through (last raw token `.streamEnd`), and that `.streamEnd` occurs exactly once. -/
def testStreamEndLastScan (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 88: S3 (c) streamEnd-last — scanFiltered output is non-empty and ends in streamEnd"
  let rows : List (String × Bool) :=
    [ ("", true), ("\uFEFF", true), ("# c\n\n", true), ("\n\n\n", true), ("---", true), ("...", true),
      ("--- a\n...\n\n\n", true), ("a", true), ("a\n", true), ("[a, [b, {c: d}]]", true), ("a:\n  b:\n    c: d", true),
      ("|\n a\n b\n", true), (">-\n a\n", true), ("%YAML 1.2\n---\na", true), ("%TAG !e! tag:x,2000:\n--- !e!a b", true),
      ("--- a\n--- b\n", true), ("--- a\n...\n--- b\n...", true), ("- a\n- - b\n  - c", true), ("? a\n: b", true),
      ("\"a\\nb\"", true), ("'a'", true), ("&x a", true), ("[&x a, *x]", true), ("!!str a", true),
      -- refused: no claim, only that the verdict is as predicted
      ("[a", false), ("%YAML 1.2\n", false), ("*x", false), ("{a", false),
      -- predicted refused, scans: ` c` on the next line continues the plain scalar `b c`
      ("a: b\n c", true) ]
  let mut scanned := 0
  let mut refused := 0
  for (input, expOk) in rows do
    match Scanner.scanFiltered input with
    | .error e =>
      refused := refused + 1
      checkM state s!"P88 {repr input}: refused" (!expOk) s!"{repr e}"
    | .ok ts =>
      scanned := scanned + 1
      let vs := ts.toList.map (·.val)
      checkM state s!"P88 {repr input}: scans" expOk s!"{ts.size} tokens"
      checkM state s!"P88 {repr input}: non-empty and last token is streamEnd"
        (ts.size > 0 && (ts[ts.size - 1]?.map (·.val)) == some .streamEnd) s!"{repr vs}"
      checkM state s!"P88 {repr input}: streamEnd occurs exactly once" ((vs.filter (· == .streamEnd)).length == 1)
        s!"{repr vs}"
      match Scanner.scan input with
      | .ok raw =>
        let rawVals := L4YAML.Proofs.DirectiveRuns.toks raw
        checkM state s!"P88 {repr input}: raw scan ends in streamEnd (the proof's intermediate)"
          (rawVals.getLast? == some .streamEnd) s!"{repr rawVals}"
      | .error e => checkM state s!"P88 {repr input}: raw scan agrees with scanFiltered" false s!"{repr e}"
  checkM state s!"P88 grid: scanned={scanned} refused={refused}" (scanned == 25 && refused == 4) ""

/-! **Priority 89 — the `.streamEnd` step of S3 (c)'s composition, instantiated BEFORE the proof
    (Rule 2).**  `parseStreamLoop` stops before consuming `.streamEnd`, so the witness `k` of
    `parseStream_ok_checkFrom` may be `ts.size - 1`, not `ts.size`; the full-array verdict
    `checkFrom {} (tokenEvents ts)` therefore needs `tokenEvents (ts.extract 0 (ts.size - 1)) =
    tokenEvents ts` — that `.streamEnd` adds no event — on top of `streamEnd`-last.  The grid checks
    that equality and the equal `checkFrom` verdicts on every scanned Priority 88 row, that
    `parseStream` accepting a row gives the full-array verdict, and — the control that the equality
    is about `.streamEnd` specifically — that dropping one more token on a row ending in `...` changes
    the events (`endDocument` is lost). -/
def testStreamEndNoEvent (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 89: S3 (c) composition — the prefix before streamEnd has the full array's events"
  let rows : List String :=
    [ "", "\uFEFF", "# c\n\n", "---", "...", "--- a\n...\n\n\n", "a", "[a, [b, {c: d}]]",
      "a:\n  b:\n    c: d", "|\n a\n b\n", "%YAML 1.2\n---\na", "%TAG !e! tag:x,2000:\n--- !e!a b",
      "--- a\n--- b\n", "--- a\n...\n--- b\n...", "- a\n- - b\n  - c", "? a\n: b", "&x a", "[&x a, *x]",
      "!!str a", "a: b\n c" ]
  let mut scanned := 0
  let mut parsed := 0
  for input in rows do
    match Scanner.scanFiltered input with
    | .error e => checkM state s!"P89 {repr input}: scans" false s!"{repr e}"
    | .ok ts =>
      scanned := scanned + 1
      let evFull := L4YAML.Proofs.Serialization.TokenEvents.tokenEvents ts
      let evPre := L4YAML.Proofs.Serialization.TokenEvents.tokenEvents (ts.extract 0 (ts.size - 1))
      checkM state s!"P89 {repr input}: events of the prefix before streamEnd = events of ts"
        (evPre == evFull) s!"{repr evPre} vs {repr evFull}"
      let cf : List L4YAML.Proofs.Serialization.SerializationWellFormed.Event → Bool :=
        fun ev => L4YAML.Proofs.Serialization.SerializationWellFormed.checkFrom
          ({} : L4YAML.Proofs.Serialization.SerializationWellFormed.Env) ev
      checkM state s!"P89 {repr input}: checkFrom agrees on that prefix and on ts"
        (cf evPre == cf evFull) ""
      match parseStream ts with
      | .ok _ =>
        parsed := parsed + 1
        checkM state s!"P89 {repr input}: parseStream ok ⇒ checkFrom \{} (tokenEvents ts)"
          (cf evFull) s!"{repr evFull}"
      | .error _ => pure ()
  for input in ["--- a\n...", "--- a\n...\n--- b\n..."] do
    match Scanner.scanFiltered input with
    | .error e => checkM state s!"P89 control {repr input}: scans" false s!"{repr e}"
    | .ok ts =>
      let evFull := L4YAML.Proofs.Serialization.TokenEvents.tokenEvents ts
      let evPre2 := L4YAML.Proofs.Serialization.TokenEvents.tokenEvents (ts.extract 0 (ts.size - 2))
      checkM state s!"P89 control {repr input}: dropping documentEnd too changes the events"
        (evPre2 != evFull) s!"{repr evPre2} vs {repr evFull}"
  checkM state s!"P89 grid: scanned={scanned} parsed={parsed}" (scanned == 20 && parsed == 20) ""

/-! **Priority 89 (ii) — `go_append_streamEnd` on its own quantified scope, instantiated BEFORE the
    proof (Rule 2).**  The lemma is `∀ l p pending, p.val = .streamEnd → go (l ++ [p]) pending = go l
    pending` for ARBITRARY token lists and pending handles — not just scanner output read with
    `pending = []`.  The grid: every token kind the fold names (`anchor`/`alias`/`tag` with named,
    empty and bare-`!` handles/`documentStart`/`documentEnd`/named and unnamed `tagDirective`/
    `versionDirective`/`scalar`/`placeholder`/`blockEntry`/`key`/`value`/`streamStart`/a mid-list
    `streamEnd`), as `[]`, `[x]`, `[x, y]` and three-token lists, under `pending ∈ {[], ["!f!"],
    ["!f!", "!g!"]}`.  Controls, so the equality is about `.streamEnd` specifically: appending
    `.documentEnd` changes every row (`endDocument`), appending `%TAG !e!` changes every row
    (`declareTag "!e!"` is flushed at the end), appending `---` changes every row. -/
def testGoAppendStreamEnd (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 89 (ii): go_append_streamEnd — arbitrary lists and pending handles"
  let go := L4YAML.Proofs.Serialization.TokenEvents.go
  let se := s5Tok .streamEnd
  let kinds : List YamlToken :=
    [ .anchor "x", .alias "x", .tag "!e!" "a", .tag "" "a", .tag "!" "a", .tag "!!" "str",
      .documentStart, .documentEnd, .tagDirective "!e!" "tag:x", .tagDirective "!" "tag:y",
      .tagDirective "!!" "tag:z", .versionDirective 1 2, .scalar "a" .plain, .placeholder,
      .blockEntry, .key, .value, .streamStart, .streamEnd, .blockMappingStart, .flowSequenceStart ]
  let pendings : List (List String) := [[], ["!f!"], ["!f!", "!g!"]]
  let singles : List (List YamlToken) := kinds.map ([·])
  let pairs : List (List YamlToken) := kinds.flatMap fun a => kinds.map fun b => [a, b]
  let triples : List (List YamlToken) :=
    [ [.documentStart, .tagDirective "!e!" "tag:x", .documentEnd],
      [.tagDirective "!e!" "tag:x", .documentStart, .anchor "a"],
      [.tagDirective "!e!" "tag:x", .tagDirective "!h!" "tag:y", .documentStart],
      [.anchor "a", .streamEnd, .alias "a"], [.tag "!e!" "a", .documentEnd, .documentStart],
      [.documentStart, .documentEnd, .streamEnd] ]
  let lists : List (List YamlToken) := [[]] ++ singles ++ pairs ++ triples
  let mut rows := 0
  let mut agree := 0
  let mut ctrlDocEnd := 0
  let mut ctrlTagDir := 0
  let mut ctrlDocStart := 0
  for l in lists do
    for pending in pendings do
      rows := rows + 1
      let ps := l.map s5Tok
      let lhs := go (ps ++ [se]) pending
      let rhs := go ps pending
      if lhs == rhs then agree := agree + 1
      else checkM state s!"P89(ii) go {repr l} {repr pending}: appending streamEnd keeps the events" false
        s!"{repr lhs} vs {repr rhs}"
      if go (ps ++ [s5Tok .documentEnd]) pending != rhs then ctrlDocEnd := ctrlDocEnd + 1
      if go (ps ++ [s5Tok (.tagDirective "!e!" "tag:x")]) pending != rhs then ctrlTagDir := ctrlTagDir + 1
      if go (ps ++ [s5Tok .documentStart]) pending != rhs then ctrlDocStart := ctrlDocStart + 1
  -- the review's literal row: `%TAG !e!` under a pending `!f!`, with and without the appended streamEnd
  let lit := [s5Tok (.tagDirective "!e!" "tag:x")]
  checkM state "P89(ii) go [%TAG !e!] [\"!f!\"] = [declareTag !f!, declareTag !e!] (pending flushed in order)"
    (go lit ["!f!"] == [.declareTag "!f!", .declareTag "!e!"]) s!"{repr (go lit ["!f!"])}"
  checkM state "P89(ii) go [%TAG !e!, streamEnd] [\"!f!\"] = go [%TAG !e!] [\"!f!\"]"
    (go (lit ++ [se]) ["!f!"] == go lit ["!f!"]) ""
  checkM state "P89(ii) go [] [\"!f!\"] = [declareTag !f!] and streamEnd alone adds nothing"
    (go [] ["!f!"] == [.declareTag "!f!"] && go [se] ["!f!"] == [.declareTag "!f!"]) ""
  checkM state s!"P89(ii) grid: rows={rows} agree={agree} (theorem-holds on every row)" (rows == 1407 && agree == rows) ""
  checkM state s!"P89(ii) controls: documentEnd changes every row ({ctrlDocEnd}), %TAG !e! changes every row ({ctrlTagDir}), --- changes every row ({ctrlDocStart})"
    (ctrlDocEnd == rows && ctrlTagDir == rows && ctrlDocStart == rows) ""

/-! **Priority 89 (iii) — `DirInv_scanLoop_streamEnd` on `scanLoop` itself: fuel 0/1/2 and states
    before and after a scanner step, instantiated BEFORE the proof (Rule 2).**  The lemma:
    `AllKeysValid s → DirInv s → scanLoop s fuel = .ok ts → ∃ L, toks ts = L ++ [.streamEnd] ∧
    .streamEnd ∉ L`, for ANY state and fuel.  The grid runs `scanLoop` directly, from the state `scan`
    builds (`mk'` + `streamStart` + BOM) and from the states one and two `scanNextToken` steps later,
    with fuel 0, 1, 2 and up to 24, on empty/BOM/scalar/`---`/`...`/flow/nested-block/directive/
    sequence inputs and a refused one.  On every `.ok` the full conclusion is checked (sole trailing
    `.streamEnd`); the decidable parts of `DirInv` (`ok`, `flag`, `dpAD`, `nose`) are checked on every
    start state.  Fuel 0 is always `fuelExhausted` (vacuous row, failed-hypothesis); the first fuel that
    succeeds is pinned per input.  The premise matters: a start state that already holds a `.streamEnd`
    (violating `nose`) scans the empty input to TWO `.streamEnd`s — refuting the conclusion without the
    hypothesis — and a start state with `directivesPresent` up is refused (`directiveWithoutDocument`). -/
def testScanLoopStreamEndFuel (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 89 (iii): DirInv_scanLoop_streamEnd — scanLoop at fuel 0/1/2 from stepped states"
  let toks := L4YAML.Proofs.DirectiveRuns.toks
  let vals := L4YAML.Proofs.DirectiveRuns.vals
  let dirRun := L4YAML.Proofs.DirectiveRuns.dirRun
  let start (input : String) : Scanner.ScannerState :=
    let s := Scanner.ScannerState.mk' input
    let s := s.emit .streamStart
    match s.peek? with
    | some '\uFEFF' => s.consumeBOM
    | _ => s
  let conclusion (ts : Array (Positioned YamlToken)) : Bool :=
    let vs := toks ts
    vs.getLast? == some .streamEnd && (vs.dropLast.filter (· == .streamEnd)).isEmpty
  let dirInvDec (s : Scanner.ScannerState) : Bool :=
    let d := dirRun false (vals s)
    d != none && (d == some true → s.directivesPresent) && (s.directivesPresent → s.allowDirectives)
      && !(vals s).contains .streamEnd
  -- (input, predicted first succeeding fuel from the start state; none = scan refuses)
  let rows : List (String × Option Nat) :=
    [ ("", some 1), ("\uFEFF", some 1), ("# c\n", some 1), ("a", some 2), ("---", some 2), ("...", some 2),
      ("--- a\n...", some 4), ("[a]", some 4), -- predicted 8, got 6: the mapping-start/key/value tokens come out of one `scanNextToken` step each
      ("a:\n  b: c", some 6), ("- a\n- b", some 5),
      ("%YAML 1.2\n---\na", some 4), ("%TAG !e! tag:x,2000:\n--- !e!a b", some 5), ("[a", none),
      ("%YAML 1.2\n", none) ]
  let maxFuel := 24
  let mut okRows := 0
  let mut fuel0 := 0
  for (input, expFirst) in rows do
    -- the start state and the states one and two scanner steps later
    let s0 := start input
    let mut starts : List (Nat × Scanner.ScannerState) := [(0, s0)]
    match Scanner.scanNextToken s0 with
    | .ok (some s1) =>
      starts := starts ++ [(1, s1)]
      match Scanner.scanNextToken s1 with
      | .ok (some s2) => starts := starts ++ [(2, s2)]
      | _ => pure ()
    | _ => pure ()
    for (step, s) in starts do
      checkM state s!"P89(iii) {repr input} step {step}: decidable DirInv parts (ok/flag/dpAD/nose) hold" (dirInvDec s)
        s!"{repr (vals s)} dp={s.directivesPresent}"
      let mut first : Option Nat := none
      let mut last : Option (List YamlToken) := none
      for fuel in List.range (maxFuel + 1) do
        match Scanner.scanLoop s fuel with
        | .error e =>
          if fuel == 0 then fuel0 := fuel0 + 1
          else if fuel == 0 then pure ()
          else if first.isSome then
            checkM state s!"P89(iii) {repr input} step {step} fuel {fuel}: success is monotone in fuel" false s!"{repr e}"
          else pure ()
        | .ok ts =>
          okRows := okRows + 1
          checkM state s!"P89(iii) {repr input} step {step} fuel {fuel}: scanLoop ok ⇒ sole trailing streamEnd"
            (conclusion ts) s!"{repr (toks ts)}"
          checkM state s!"P89(iii) {repr input} step {step} fuel {fuel}: fuel 0 never succeeds" (fuel > 0) ""
          if first.isNone then first := some fuel
          match last with
          | some prev => checkM state s!"P89(iii) {repr input} step {step} fuel {fuel}: more fuel, same tokens" (prev == toks ts) ""
          | none => pure ()
          last := some (toks ts)
      if step == 0 then
        checkM state s!"P89(iii) {repr input}: first succeeding fuel from the start state is {repr expFirst}"
          (first == expFirst) s!"got {repr first}"
      else
        -- a stepped state needs exactly one unit of fuel less per step taken
        checkM state s!"P89(iii) {repr input} step {step}: first succeeding fuel = start's − {step}"
          (first == expFirst.map (· - step)) s!"got {repr first}"
  -- the premise matters: `nose` violated ⇒ two streamEnds; `directivesPresent` up ⇒ refused
  let bad := (start "").emit .streamEnd
  match Scanner.scanLoop bad 1 with
  | .ok ts =>
    checkM state "P89(iii) without nose: scanLoop from a state already holding streamEnd succeeds with TWO streamEnds — the conclusion fails"
      (!conclusion ts && (toks ts).count .streamEnd == 2) s!"{repr (toks ts)}"
  | .error e => checkM state "P89(iii) without nose: scanLoop succeeds" false s!"{repr e}"
  let dp := { start "" with directivesPresent := true }
  match Scanner.scanLoop dp 1 with
  | .ok ts => checkM state "P89(iii) directivesPresent up on empty input: refused" false s!"{repr (toks ts)}"
  | .error e => checkM state "P89(iii) directivesPresent up on empty input: directiveWithoutDocument"
      (match e with | .directiveWithoutDocument _ => true | _ => false) s!"{repr e}"
  checkM state s!"P89(iii) grid: okRows={okRows} fuel0Errors={fuel0}" (okRows > 0 && fuel0 > 0) s!"okRows={okRows} fuel0={fuel0}"

/-! **Priority 91 — S3 (d), the loop's no-progress exit on scanner output, instantiated BEFORE the
    proof (Rule 2).**  Naive (d) — "for S5's witness `k`, `StuckAt ts k` is impossible on scanner
    output, so only `k = ts.size` is reachable" — is FALSE as stated: `StuckAt` is a property of a
    token index with no tie to the loop, and it holds at index 0 of every output (`.streamStart` is an
    `emptyFollowerTok`), at every `.key`/`.value`/`---`/`...` index (`a: b`: k = 2, 4) and at the
    second `-` of `-\n- a` (k = 3), each with S5's prefix verdict true — so no scanner fact can
    exclude the disjunct as stated ((i), pinned).  The strongest true statement ties `k` to the loop:
    `StuckAt ts k ∧ (k = ps.pos ∨ tok ts (k-1) = some .documentEnd ∨
       validNextToken .afterDocument (tok ts k) = true)` — the stuck exit is the first iteration,
    follows a consumed `...`, or sits in the `.afterDocument` state whose `validNextToken` admitted
    the token.  (ii) shadows `parseStreamLoop` (same peek / `parseDocument` / `tryConsume` / state
    transitions), checks it agrees with the real loop, and records where `parseDocument` is called
    and where the loop stops: on scanner output the stop is always the `.streamEnd` index, the
    no-progress exit is never taken, and the document-start tokens are `bM`/`bS`/`[`/`{`/scalar/
    `---`/`%YAML`/anchor/tag (counts pinned), never key/value/blockEnd/flowEntry/flow-end.  (iii)
    pins the refined disjunct as NOT a tautology — false at the anchor and alias of `[&x a, *x]`, the
    tag of `[!t a]`, the second `-` of `-\n- a` — and records the residue (γ): it is TRUE at the
    `.value` of `a: b` (k = 4) because `validNextToken .afterDocument .value = true`; excluding that
    needs a bracket-depth argument on both sides.  (iv) drives `parseStreamLoop` directly at fuel
    0/1/2 (and `ts.size`) from `.initial`/`.afterDocument`/`.afterDocumentEnd` at first/middle/last
    positions, checking the refined conclusion whenever `size < fuel + pos` holds and that the
    premise is not vacuous (fuel 0 on `a: b` stops at the `bM`); the `k = ps.pos` disjunct is
    witnessed by starting at the `.value` of `a: b`. -/
namespace P91
open L4YAML.Proofs.Serialization.ParseCheckFrom (tok emptyFollowerTok)

def stuckAtB (ts : Array (Positioned YamlToken)) (k : Nat) : Bool :=
  emptyFollowerTok (tok ts k) ||
    (tok ts k == some .blockEntry && decide (0 < k) && tok ts (k - 1) == some .blockEntry)

def afterDocOK : Option YamlToken → Bool
  | some t => StreamState.validNextToken .afterDocument t
  | none => false

def stateOK (st : StreamState) : Option YamlToken → Bool
  | some t => st.validNextToken t
  | none => false

/-- the refined disjunct's second conjunct, state-aware (the loop lemma's form) -/
def stopShapeB (ts : Array (Positioned YamlToken)) (st : StreamState) (p k : Nat) : Bool :=
  (k == p && stateOK st (tok ts k)) || tok ts (k - 1) == some .documentEnd || afterDocOK (tok ts k)

def conclB (ts : Array (Positioned YamlToken)) (st : StreamState) (p k : Nat) : Bool :=
  k == ts.size || tok ts k == some .streamEnd || (stuckAtB ts k && stopShapeB ts st p k)

/-- the refined disjunct at `parseStream`'s top level (pos 1, `.initial`) -/
def loopStuckB (ts : Array (Positioned YamlToken)) (k : Nat) : Bool :=
  stuckAtB ts k && (k == 1 || tok ts (k - 1) == some .documentEnd || afterDocOK (tok ts k))

def dead : Option YamlToken → Bool
  | some .key | some .value | some .blockEnd | some .flowEntry | some .flowSequenceEnd
  | some .flowMappingEnd | some .streamStart | none => true
  | _ => false

def tokName : Option YamlToken → String
  | some .streamStart => "SS" | some .streamEnd => "SE" | some .documentStart => "DS"
  | some .documentEnd => "DE" | some (.versionDirective ..) => "%Y" | some (.tagDirective ..) => "%T"
  | some (.scalar ..) => "sc" | some .blockSequenceStart => "bS" | some .blockMappingStart => "bM"
  | some .blockEnd => "bE" | some .blockEntry => "-" | some .flowSequenceStart => "["
  | some .flowSequenceEnd => "]" | some .flowMappingStart => "{" | some .flowMappingEnd => "}"
  | some .flowEntry => "," | some .key => "?" | some .value => ":" | some (.anchor ..) => "&"
  | some (.alias ..) => "*" | some (.tag ..) => "!" | some _ => "??" | none => "∅"

def stName : StreamState → String
  | .initial => "initial" | .afterDocument => "afterDocument" | .afterDocumentEnd => "afterDocumentEnd"

structure Shadow where
  visited : List Nat
  stop : Nat
  state : StreamState
  stuck : Bool := false
  err : Bool := false

/-- `parseStreamLoop`'s control flow with the positions it visits and the state at the stop. -/
def shadow (ts : Array (Positioned YamlToken)) :
    Nat → ParseState → StreamState → List Nat → Shadow
  | 0, ps, st, vis => { visited := vis.reverse, stop := ps.pos, state := st }
  | f + 1, ps, st, vis =>
    match ps.peek? with
    | some .streamEnd => { visited := vis.reverse, stop := ps.pos, state := st }
    | none => { visited := vis.reverse, stop := ps.pos, state := st }
    | some .documentEnd => shadow ts f (ps.tryConsume .documentEnd).2 .afterDocumentEnd vis
    | some t =>
      if !st.validNextToken t then
        { visited := vis.reverse, stop := ps.pos, state := st, err := true }
      else
        match parseDocument ps with
        | .error _ => { visited := vis.reverse, stop := ps.pos, state := st, err := true }
        | .ok (_, ps') =>
          let ps2 : ParseState :=
            { ps' with anchors := #[], anchorIndex := .empty, declaredAnchors := #[],
                       declaredIndex := .empty, nodePositions := #[], currentPath := #[] }
          let (c, ps3) := ps2.tryConsume .documentEnd
          if ps3.pos == ps.pos then
            { visited := (ps.pos :: vis).reverse, stop := ps.pos, state := st, stuck := true }
          else shadow ts f ps3 (if c then .afterDocumentEnd else .afterDocument) (ps.pos :: vis)

def at_ (ts : Array (Positioned YamlToken)) (p : Nat) : ParseState :=
  { ParseState.mk' ts with pos := p }

/-- The loop's refusal of a no-progress exit ((γ2α)): `trailingContent`. -/
def isTrailing : Except ScanError (Array YamlDocument) → Bool
  | .error (.trailingContent ..) => true
  | _ => false

def isTrailingM : Except ScanError (Array L4YAML.Events.MarkedDoc) → Bool
  | .error (.trailingContent ..) => true
  | _ => false

def rows : List String :=
  [ "", "a", "a: b", "---", "...", "--- a", "--- a\n...", "- - a", "- - - a", "-\n- a", "- \n  - a",
    ": a", "? a", "? a\n: b", "]", "}", ",", "*x", "&x", "&x a", "!!str", "!t a", "%YAML 1.2\n---",
    "...\n: a", "...\n? a", "...\n]", "...\n}", "...\n,", "...\n*x", "...\n&x a", "...\n!!str a",
    "...\n%YAML 1.2\n---", "...\n---", "...\n...", "...\n- a", "...\n- - a", "...\n:", "...\n-",
    "a\n...\n: b\n...\nc", "---\n: a", "--- : a", "---\n? a", "--- ]", "--- ,", "--- }", "---\n- - a",
    "--- - - a", "--- -\n- a", "a\n: b", "[a]\n]", "[a]\n,", "a: b\nc", "a: b\n: c", "{a: b}\n}",
    "[a]\n: b", "a\n...\n]", "a\n...\n:", "--- a\n--- : b", "--- a\n---\n: b", "- a\n...\n- - b", ": ",
    ":", "?", "? ", "-", "- ", "--- -", "--- ?", "--- :", "...\n?", "a:\n- b", "a:\n- - b",
    "- ? a\n  : b", "- : a", "[: a]", "{: a}", "[? a]", "&a\n...\n*a", "*a\n...", "!t\n...\n!t",
    "--- &a\n--- *a", "\uFEFF: a", "# c\n: a", "\n\n: a", "   : a", "  - - a" ]

def bump (acc : List (String × Nat)) (k : String) : List (String × Nat) :=
  match acc.find? (·.1 == k) with
  | some _ => acc.map fun (a, n) => if a == k then (a, n + 1) else (a, n)
  | none => acc ++ [(k, 1)]

/-- every token list of length ≤ n over `kinds` -/
def lists (kinds : List YamlToken) : Nat → List (List YamlToken)
  | 0 => [[]]
  | n + 1 =>
    let r := lists kinds n
    r ++ (r.filter (·.length == n)).flatMap fun l => kinds.map (· :: l)

def mkArr (l : List YamlToken) : Array (Positioned YamlToken) :=
  (l.map fun t => { pos := { offset := 0, line := 0, col := 0 }, val := t }).toArray

end P91

def testStuckAtDocStart (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 91: S3 (d) — StuckAt at the loop's stop: refutation and the refined disjunct"
  let cf : Array (Positioned YamlToken) → Nat → Bool := fun ts k =>
    L4YAML.Proofs.Serialization.SerializationWellFormed.checkFrom
      ({} : L4YAML.Proofs.Serialization.SerializationWellFormed.Env)
      (L4YAML.Proofs.Serialization.TokenEvents.tokenEvents (ts.extract 0 k))
  let tk := L4YAML.Proofs.Serialization.ParseCheckFrom.tok
  let isOk : Except ScanError (Array YamlDocument) → Bool := fun r =>
    match r with | .ok _ => true | .error _ => false
  let mut scanned := 0
  let mut parsed := 0
  let mut refused := 0
  let mut loopPos := 0
  let mut classes : List (String × Nat) := []
  for input in P91.rows do
    match Scanner.scanFiltered input with
    | .error _ => refused := refused + 1
    | .ok ts =>
      scanned := scanned + 1
      -- (i) the naive form is refuted at k = 0 on every output: StuckAt, not size, not streamEnd,
      -- and S5's prefix verdict holds there
      checkM state s!"P91(i) {repr input}: StuckAt ts 0 ∧ 0 ≠ size ∧ tok 0 ≠ streamEnd ∧ checkFrom on the empty prefix"
        (P91.stuckAtB ts 0 && 0 != ts.size && tk ts 0 != some .streamEnd && cf ts 0) ""
      -- (ii) the shadow against the real loop, from parseStream's start (pos 1, .initial, fuel size)
      let sh := P91.shadow ts ts.size (P91.at_ ts 1) .initial []
      let real := parseStreamLoop (P91.at_ ts 1) #[] .initial ts.size
      checkM state s!"P91(ii) {repr input}: shadow success agrees with parseStreamLoop"
        (sh.err == !isOk real) s!"shadow err={sh.err}"
      checkM state s!"P91(ii) {repr input}: shadow success agrees with parseStream"
        (sh.err == !isOk (parseStream ts)) ""
      if isOk (parseStream ts) then
        parsed := parsed + 1
        checkM state s!"P91(ii) {repr input}: no no-progress exit; stop is the streamEnd index"
          (!sh.stuck && sh.stop + 1 == ts.size && tk ts sh.stop == some .streamEnd)
          s!"stuck={sh.stuck} stop={sh.stop} size={ts.size}"
        checkM state s!"P91(ii) {repr input}: refined conclusion at the stop"
          (P91.conclB ts sh.state 1 sh.stop) ""
      for p in sh.visited do
        loopPos := loopPos + 1
        classes := P91.bump classes (P91.tokName (tk ts p))
        checkM state s!"P91(ii) {repr input}: document-start token at {p} is live ({P91.tokName (tk ts p)})"
          (!P91.dead (tk ts p)) ""
        checkM state s!"P91(ii) {repr input}: StuckAt at document start {p} only for a head-consumed token"
          (!P91.stuckAtB ts p || (match tk ts p with
            | some .documentStart | some (.versionDirective ..) | some (.tagDirective ..)
            | some (.anchor ..) | some (.tag ..) | some (.alias ..) => true
            | _ => false)) s!"{P91.tokName (tk ts p)}"
  checkM state s!"P91 grid: rows={P91.rows.length} scanned={scanned} refused={refused} parsed={parsed} loopPositions={loopPos}"
    (P91.rows.length == 86 && scanned == 58 && refused == 28 && parsed == 58 && loopPos == 61)
    "prediction corrected: 56 scanned / 30 refused was a miscount of the probe; every scanned row parses"
  let expected : List (String × Nat) :=
    [("bM", 21), ("bS", 14), ("DS", 9), ("!", 5), ("sc", 4), ("&", 3), ("%Y", 2), ("[", 2), ("{", 1)]
  for (c, n) in expected do
    checkM state s!"P91(ii) document-start class {c}: {n} occurrences"
      ((classes.find? (·.1 == c)).map (·.2) == some n) s!"{repr classes}"
  checkM state s!"P91(ii) no other document-start class" (classes.length == expected.length) s!"{repr classes}"
  -- (i)/(iii) pins
  let pinRow := fun (input : String) (f : Array (Positioned YamlToken) → IO Unit) => do
    match Scanner.scanFiltered input with
    | .error e => checkM state s!"P91 pin {repr input}: scans" false s!"{repr e}"
    | .ok ts => f ts
  pinRow "a: b" fun ts => do
    checkM state "P91(i) \"a: b\": StuckAt at the key (2) and the value (4), prefix verdicts true"
      (P91.stuckAtB ts 2 && P91.stuckAtB ts 4 && cf ts 2 && cf ts 4 && tk ts 4 == some .value) ""
    checkM state "P91(iii) residue (γ): the refined disjunct HOLDS at the value of \"a: b\" (afterDocument admits .value)"
      (P91.loopStuckB ts 4 && P91.afterDocOK (some .value)) ""
    checkM state "P91(iii) \"a: b\": refined disjunct false at the key's scalar (3, not StuckAt)"
      (!P91.loopStuckB ts 3) ""
  pinRow "-\n- a" fun ts => do
    checkM state "P91(i) \"-\\n- a\": StuckAt at 3 by the blockEntry-after-blockEntry disjunct, prefix verdict true"
      (tk ts 2 == some .blockEntry && tk ts 3 == some .blockEntry && P91.stuckAtB ts 3 && cf ts 3) ""
    checkM state "P91(iii) \"-\\n- a\": refined disjunct false at 3" (!P91.loopStuckB ts 3) ""
  pinRow "[&x a, *x]" fun ts => do
    checkM state "P91(iii) \"[&x a, *x]\": StuckAt at the anchor (2) and alias (5), refined disjunct false at both"
      (tk ts 2 == some (.anchor "x") && tk ts 5 == some (.alias "x") && P91.stuckAtB ts 2 &&
        P91.stuckAtB ts 5 && !P91.loopStuckB ts 2 && !P91.loopStuckB ts 5) s!"{repr (ts.map (·.val))}"
  pinRow "[!t a]" fun ts => do
    checkM state "P91(iii) \"[!t a]\": StuckAt at the tag (2), refined disjunct false"
      (P91.stuckAtB ts 2 && !P91.loopStuckB ts 2) s!"{repr (ts.map (·.val))}"
  pinRow "--- a\n--- b" fun ts => do
    checkM state "P91(iii) \"--- a\\n--- b\": the second --- (3) is StuckAt and satisfies the refined disjunct (afterDocument admits ---)"
      (tk ts 3 == some .documentStart && P91.loopStuckB ts 3) ""
  -- (iv) parseStreamLoop directly: fuel 0/1/2/size, three states, first/middle/last positions
  let fuelRows : List String := ["", "a", "a: b", "--- a\n--- b", "a\n...\n: b\n...\nc", "-\n- a", "[&x a, *x]", "...\n..."]
  let states : List StreamState := [.initial, .afterDocument, .afterDocumentEnd]
  let mut instances := 0
  let mut holds := 0
  let mut vacuous := 0
  let mut nonVacuous := 0
  for input in fuelRows do
    match Scanner.scanFiltered input with
    | .error e => checkM state s!"P91(iv) {repr input}: scans" false s!"{repr e}"
    | .ok ts =>
      let positions := ([1, 2, ts.size / 2, ts.size - 1, ts.size] ++ (if input == "a: b" then [4] else [])).eraseDups
      for st in states do
        for p in positions do
          for f in [0, 1, 2, ts.size] do
            let real := parseStreamLoop (P91.at_ ts p) #[] st f
            let sh := P91.shadow ts f (P91.at_ ts p) st []
            instances := instances + 1
            -- since (γ2α) the loop refuses where the shadow reports a no-progress exit
            checkM state s!"P91(iv) {repr input} st={P91.stName st} pos={p} fuel={f}: shadow agrees with the loop"
              ((sh.err || sh.stuck) == !isOk real) ""
            if isOk real then
              let premise := ts.size < f + p
              let concl := P91.conclB ts sh.state p sh.stop
              if premise then
                holds := holds + 1
                checkM state s!"P91(iv) {repr input} st={P91.stName st} pos={p} fuel={f}: refined conclusion at stop {sh.stop}"
                  concl s!"stuck={sh.stuck} state={P91.stName sh.state} tok={P91.tokName (tk ts sh.stop)}"
              else if concl then vacuous := vacuous + 1
              else nonVacuous := nonVacuous + 1
  checkM state s!"P91(iv) instances={instances} premise-holds={holds} premise-fails∧concl={vacuous} premise-fails∧¬concl={nonVacuous}"
    (nonVacuous > 0) ""
  match Scanner.scanFiltered "a: b" with
  | .error _ => pure ()
  | .ok ts =>
    let sh0 := P91.shadow ts 0 (P91.at_ ts 1) .initial []
    checkM state "P91(iv) \"a: b\" fuel 0: loop returns ok at the bM (k = 1), the conclusion fails — the size < fuel + pos premise is load-bearing"
      (isOk (parseStreamLoop (P91.at_ ts 1) #[] .initial 0) && sh0.stop == 1 &&
        !P91.conclB ts .initial 1 1) ""
    for st in states do
      let sh4 := P91.shadow ts ts.size (P91.at_ ts 4) st []
      checkM state s!"P91(iv) \"a: b\" from the value (4), {P91.stName st}: the shadow takes the no-progress exit at k = pos (the k = ps.pos shape); since (γ2α) the loop refuses it as `trailingContent`"
        (P91.isTrailing (parseStreamLoop (P91.at_ ts 4) #[] st ts.size) && sh4.stuck && sh4.stop == 4 &&
          P91.stuckAtB ts 4 && P91.conclB ts st 4 4) ""
/-! **Priority 92 — S3 (β), the document-start token on scanner output, instantiated BEFORE the
    proof (Rule 2).**  Statement to prove: `scanFiltered input = .ok ts →` the token at index 1 and the
    token right after every `.documentEnd` is never dead — `key` / `value` / `blockEnd` / `flowEntry` /
    `flowSequenceEnd` / `flowMappingEnd` / `streamStart` (nor absent).  The raw shape the invariant
    carries: for a dead raw token at `j`, `prevRealIdx? raw j` (the nearest non-placeholder before it)
    is never `streamStart` / `documentEnd`; placeholders are the only tokens between a reservation
    and its filled `key`.  (i) checks both on 86 + 40 inputs (index 1 and after `...`: every token
    kind, BOM / comment / blank prefixes, `...` runs, `...` with trailing comment, `--- ...`, block
    scalars and quoted scalars after `...`, flow collections after `...`); (ii) drives `scanLoop`
    directly at fuel 0..24 from the start state and 1–2 steps later, checking the conclusion on every
    success; (iii) the parser side the discharge needs — `DeadAt`: on `[SS, t, SE]` for every token
    kind `t`, `parseStreamLoop` takes its no-progress exit iff `t` is dead (the head-consumed
    `emptyFollowerTok`s — `---`, directives, anchor, tag, alias — make progress or fail), likewise on
    `[SS, DE, t, SE]` and, in `.afterDocument`, on `[SS, sc, t, SE]` from position 2; (iv) the
    list-level lemmas of `Proofs/Scanner/DocStartLive.lean` directly (`filter_getLast`,
    `lastReal_snoc`, `Shape_snoc`, `LiveF_of_Shape`) on every list of length ≤ 3 over an alphabet
    with both boundaries, a placeholder, dead and live tokens, with the withdrawn-`Shape` control;
    (v) the parser progress lemmas `parseNodeProperties_progress`, `parseNode_alias_progress`,
    `parseNode_dead` on their own premises: hand-built arrays at first / middle / after-`-` / last
    positions, property orderings and an alias as the head, every token kind as the follower,
    `parseNode` fuel 0..5, premise-held and premise-failed rows tallied separately.
    (i) grew to 143 rows: `---` / `...` inside flow collections and quoted / block scalars — the only
    way a dead token could follow a boundary — are refused (`documentMarkerInFlow` /
    `documentMarkerInScalar`). -/
namespace P92
open L4YAML.Proofs.Serialization.ParseCheckFrom (tok)

def deadTok : Option YamlToken → Bool
  | some .key | some .value | some .blockEnd | some .flowEntry | some .flowSequenceEnd
  | some .flowMappingEnd | some .streamStart | some (.comment ..) | some .placeholder | none => true
  | _ => false

/-- (i) on the filtered array: index 1 and every index after a `.documentEnd` is live -/
def docStartLive (ts : Array (Positioned YamlToken)) : Bool :=
  !deadTok (tok ts 1) &&
    (List.range ts.size).all fun k => k == 0 || tok ts (k - 1) != some .documentEnd || !deadTok (tok ts k)

/-- the raw shape: a dead raw token is never preceded (through placeholders) by SS / DE -/
def rawShape (raw : Array (Positioned YamlToken)) : Bool :=
  (List.range raw.size).all fun j =>
    j == 0 || !deadTok (tok raw j) || tok raw j == some .placeholder ||
      (match prevRealIdx? raw j with
        | some i => tok raw i != some .streamStart && tok raw i != some .documentEnd
        | none => false)

def deCount (ts : Array (Positioned YamlToken)) : Nat :=
  (List.range ts.size).countP fun k => tok ts k == some .documentEnd

def extraRows : List String :=
  [ "\uFEFF...\n: a", "# c\n...\n: a", "...\n\n\n: a", "...\n...\n: a", "... # c\n: a", "--- ...",
    "--- ...\n? a", "?\n: ", "-\n...\n-", "[a]\n...\n]", "[a]\n...\n[b]", "{a: b}\n...\n{c: d}",
    "...\n|\n a", "...\n>\n a", "...\n\"a\"", "...\n'a'", "a\n...\n...\nb", "...\n%TAG !e! tag:x\n---",
    "...\n# only comment", "... ", "...\t", "...a", "....", "...\n: ", "...\n? ", "...\n- ",
    "...\n[a, b]", "...\n{a: b}", "...\n[]", "...\n{}", "...\n- - a", "...\n--- a\n...", "...\n---\n...",
    "a: b\n...\nc: d", "a: b\n...\n: d", "- a\n...\n- b", "? a\n...\n? b", "&x a\n...\n&x b",
    "!t a\n...\n!t b", "a\n...\n...\n...\nb",
    -- document markers inside flow / quoted scalars: the scanner refuses (`documentMarkerInFlow`,
    -- `documentMarkerInScalar`) — the only way a dead token could follow `...`
    "[a\n...\n]", "[\n...\n]", "{\n...\n}", "[a,\n...\nb]", "[a\n---\n]", "- [a\n...\n]",
    "\"a\n...\nb\"", "'a\n...\nb'", "|\n...\n", "a:\n...\n b", "? a\n...\n: b", "- a\n...\n  - b",
    "[a\n...", "{a\n...", "[a,\n...", "a: [\n...\n]", "a: b\n...\n c" ]

/-- executable mirror of `DocStartLive.Shape` (raw list) -/
def shapeB (L : List YamlToken) : Bool :=
  (List.range L.length).all fun j => j == 0 ||
    (match L[j]? with
     | some t => L4YAML.Proofs.DocStartLive.liveTok t || !L4YAML.Proofs.DirectiveRuns.nonPh t ||
         L4YAML.Proofs.DocStartLive.Bnd (L4YAML.Proofs.DocStartLive.lastReal (L.take j)) == false
     | none => true)

/-- executable mirror of `DocStartLive.LiveF` (filtered list) -/
def liveFB (F : List YamlToken) : Bool :=
  (List.range F.length).all fun k => k == 0 ||
    (match F[k]? with
     | some t => L4YAML.Proofs.DocStartLive.liveTok t ||
         (match F[k - 1]? with
          | some u => L4YAML.Proofs.DocStartLive.Bnd (some u) == false
          | none => false)
     | none => true)

def kinds : List (String × YamlToken) :=
  [ ("SS", .streamStart), ("SE", .streamEnd), ("ph", .placeholder), ("%Y", .versionDirective 1 2),
    ("%T", .tagDirective "!e!" "tag:x"), ("DS", .documentStart), ("DE", .documentEnd),
    ("bS", .blockSequenceStart), ("bM", .blockMappingStart), ("bE", .blockEnd), ("-", .blockEntry),
    ("?", .key), (":", .value), ("[", .flowSequenceStart), ("]", .flowSequenceEnd),
    ("{", .flowMappingStart), ("}", .flowMappingEnd), (",", .flowEntry), ("&", .anchor "x"),
    ("*", .alias "x"), ("!", .tag "!!" "str"), ("sc", .scalar "a" .plain), ("#", .comment "c") ]

end P92

def testDocStartLive (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 92: S3 (β) — the document-start token is never dead; DeadAt on the parser side"
  let rows := P91.rows ++ P92.extraRows
  let mut scanned := 0
  let mut refused := 0
  let mut des := 0
  for input in rows do
    match Scanner.scanFiltered input, Scanner.scan input with
    | .ok ts, .ok raw =>
      scanned := scanned + 1
      des := des + P92.deCount ts
      checkM state s!"P92(i) {repr input}: index 1 and every token after `...` is live"
        (P92.docStartLive ts) s!"{repr (ts.map (·.val))}"
      checkM state s!"P92(i) {repr input}: raw shape — no dead raw token right after SS / DE through placeholders"
        (P92.rawShape raw) s!"{repr (raw.map (·.val))}"
    | .error _, .error _ => refused := refused + 1
    | _, _ => checkM state s!"P92(i) {repr input}: scan and scanFiltered agree on success" false ""
  checkM state s!"P92(i) rows={rows.length} scanned={scanned} refused={refused} documentEnds={des}"
    (rows.length == 143 && scanned == 102 && refused == 41 && des == 65)
    "prediction corrected: 94 scanned / 32 refused was the guess; `...a`, `....`, `...\t` scan (plain scalars / `...` + tab)"
  -- (ii) scanLoop directly: fuel 0..24 from the start state and after one / two steps
  let mut okRuns := 0
  let mut fuelOut := 0
  for input in ["", "...", "...\n: a", "a: b\n...\nc: d", "? a\n...\n? b", "[a]\n...\n[b]", "--- ...\n? a", "-\n...\n-"] do
    let s0 := (ScannerState.mk' input).emit .streamStart
    let s0 := match s0.peek? with | some '\uFEFF' => s0.consumeBOM | _ => s0
    let steps : List (Nat × Option ScannerState) :=
      let s1 := match scanNextToken s0 with | .ok (some s) => some s | _ => none
      let s2 := s1.bind fun s => match scanNextToken s with | .ok (some s') => some s' | _ => none
      [(0, some s0), (1, s1), (2, s2)]
    for (n, st?) in steps do
      match st? with
      | none => pure ()
      | some st =>
        for fuel in List.range 25 do
          match scanLoop st fuel with
          | .error _ => fuelOut := fuelOut + 1
          | .ok raw =>
            okRuns := okRuns + 1
            let ts := raw.filter fun t => t.val != .placeholder
            checkM state s!"P92(ii) {repr input} step {n} fuel {fuel}: success ⇒ document-start tokens live (filtered) and raw shape"
              (P92.docStartLive ts && P92.rawShape raw) s!"{repr (ts.map (·.val))}"
  checkM state s!"P92(ii) scanLoop runs: ok={okRuns} fuel-out/error={fuelOut}" (okRuns > 0 && fuelOut > 0) ""
  -- (iii) DeadAt on the parser side: [SS, t, SE], [SS, DE, t, SE] from .initial / .afterDocumentEnd,
  -- [SS, sc, t, SE] from position 2 in .afterDocument — the loop's no-progress exit iff `t` is dead
  let isOk : Except ScanError (Array YamlDocument) → Bool := fun r =>
    match r with | .ok _ => true | .error _ => false
  let mut stuckDead := 0
  let mut liveProgress := 0
  let mut liveError := 0
  for (nm, t) in P92.kinds do
    for (lbl, arr, p, st) in
        [ ("[SS, t, SE]", P91.mkArr [.streamStart, t, .streamEnd], 1, StreamState.initial),
          ("[SS, DE, t, SE]", P91.mkArr [.streamStart, .documentEnd, t, .streamEnd], 1, StreamState.initial),
          ("[SS, sc, t, SE] afterDocument", P91.mkArr [.streamStart, .scalar "a" .plain, t, .streamEnd], 2,
            StreamState.afterDocument) ] do
      let real := parseStreamLoop (P91.at_ arr p) #[] st arr.size
      let sh := P91.shadow arr arr.size (P91.at_ arr p) st []
      let dead := P92.deadTok (some t) && t != .streamEnd && t != .documentEnd
      -- the loop never calls parseDocument on DE / SE / none: those are its own arms
      if sh.stuck then stuckDead := stuckDead + 1
      else if isOk real then liveProgress := liveProgress + 1
      else liveError := liveError + 1
      checkM state s!"P92(iii) {lbl} t={nm}: no-progress exit ⇔ dead token (stuck={sh.stuck} ok={isOk real})"
        (if sh.stuck then dead else
          -- a live token either progresses, is refused, or is not admitted by the state
          !dead || !(st.validNextToken t) || t == .streamEnd || t == .documentEnd)
        s!"stop={sh.stop} err={sh.err}"
  checkM state s!"P92(iii) stuck-on-dead={stuckDead} live-progress={liveProgress} live-error/not-admitted={liveError}"
    (stuckDead > 0 && liveProgress > 0 && liveError > 0) ""

  -- (iv) the list-level lemmas of `DocStartLive` directly: every list of length ≤ 3 over an
  -- alphabet with both boundaries, a placeholder, dead and live tokens; withdrawn-premise control
  let alpha : List YamlToken := [.streamStart, .documentEnd, .placeholder, .key, .scalar "a" .plain,
    .blockEnd, .blockEntry, .documentStart]
  let lists : List (List YamlToken) :=
    [[]] ++ alpha.map ([·]) ++ (alpha.flatMap fun a => alpha.map fun b => [a, b]) ++
      (alpha.flatMap fun a => alpha.flatMap fun b => alpha.map fun c => [a, b, c])
  let mut shapeOk := 0
  let mut shapeFail := 0
  let mut snocPrem := 0
  for L in lists do
    checkM state s!"P92(iv) filter_getLast {repr L}"
      (L4YAML.Proofs.DocStartLive.lastReal L ==
        (L.filter L4YAML.Proofs.DirectiveRuns.nonPh).getLast?) ""
    for t in alpha do
      checkM state s!"P92(iv) lastReal_snoc {repr L} ++ [{repr t}]"
        (L4YAML.Proofs.DocStartLive.lastReal (L ++ [t]) ==
          (if L4YAML.Proofs.DirectiveRuns.nonPh t then some t
           else L4YAML.Proofs.DocStartLive.lastReal L)) ""
      if P92.shapeB L && (L4YAML.Proofs.DocStartLive.liveTok t ||
          !L4YAML.Proofs.DirectiveRuns.nonPh t ||
          L4YAML.Proofs.DocStartLive.Bnd (L4YAML.Proofs.DocStartLive.lastReal L) == false) then
        snocPrem := snocPrem + 1
        checkM state s!"P92(iv) Shape_snoc {repr L} ++ [{repr t}]" (P92.shapeB (L ++ [t])) ""
    if P92.shapeB L then
      shapeOk := shapeOk + 1
      checkM state s!"P92(iv) LiveF_of_Shape {repr L}"
        (P92.liveFB (L.filter L4YAML.Proofs.DirectiveRuns.nonPh)) ""
    else
      shapeFail := shapeFail + 1
  checkM state s!"P92(iv) lists={lists.length} shape-ok={shapeOk} shape-fail={shapeFail} Shape_snoc-premise={snocPrem}"
    (lists.length == 585 && shapeOk > 0 && shapeFail > 0 && snocPrem > 0) ""
  let liveFails := lists.filter fun L =>
    !P92.shapeB L && !P92.liveFB (L.filter L4YAML.Proofs.DirectiveRuns.nonPh)
  checkM state s!"P92(iv) withdrawn Shape ⇒ LiveF fails on {liveFails.length} lists (first: {repr liveFails.head?})"
    (liveFails.length > 0) ""

  -- (v) the parser progress lemmas directly, on their own premises (Rule 2): hand-built arrays,
  -- first / middle / after-`-` / last positions, property orderings and an alias as the head,
  -- every token kind as the follower, `parseNode` fuel 0..5; premise-held and premise-failed rows
  -- tallied separately (and, for `parseNodeProperties_progress`, the no-progress rows the
  -- withdrawn premise admits)
  let pcf := L4YAML.Proofs.Serialization.ParseCheckFrom.emptyFollowerTok
  let heads : List (String × List YamlToken) :=
    [ ("&x", [.anchor "x"]), ("!t", [.tag "!" "t"]), ("&x !t", [.anchor "x", .tag "!" "t"]),
      ("!t &x", [.tag "!" "t", .anchor "x"]), ("&x &y", [.anchor "x", .anchor "y"]),
      ("!t !u", [.tag "!" "t", .tag "!" "u"]), ("*x", [.alias "x"]), ("(none)", []) ]
  let ctxs : List (String × List YamlToken × Nat × List YamlToken) :=
    [ ("first", [.streamStart], 1, [.streamEnd]),
      ("middle", [.streamStart, .scalar "a" .plain], 2, [.streamEnd]),
      ("after -", [.streamStart, .blockSequenceStart, .blockEntry], 3, [.blockEnd, .streamEnd]),
      ("last", [.streamStart], 1, []) ]
  let mut propHeld := 0
  let mut propFail := 0
  let mut propCtrl := 0
  let mut aliasHeld := 0
  let mut aliasFail := 0
  let mut deadHeld := 0
  let mut deadFail := 0
  for (cn, pre, p, post) in ctxs do
    for (hn, hd) in heads do
      for (fn, f) in P92.kinds do
        let arr := P91.mkArr (pre ++ hd ++ [f] ++ post)
        let ps := ((P91.at_ arr p).declareAnchor "x").addAnchor "x" (seqv [])
        let lbl := s!"P92(v) {cn} {hn} {fn}"
        let isProp := match ps.peek? with
          | some (.anchor _) => true
          | some (.tag _ _) => true
          | _ => false
        match parseNodeProperties ps with
        | .ok (_, ps') =>
          if isProp then
            propHeld := propHeld + 1
            checkM state s!"{lbl}: parseNodeProperties_progress" (ps.pos < ps'.pos)
              s!"pos {ps.pos} → {ps'.pos}"
          else
            propFail := propFail + 1
            if !(ps.pos < ps'.pos) then propCtrl := propCtrl + 1
        | .error _ => propFail := propFail + 1
        for m in List.range 6 do
          match parseNode ps m with
          | .error _ =>
            aliasFail := aliasFail + 1
            deadFail := deadFail + 1
          | .ok (_, ps') =>
            match ps.peek? with
            | some (.alias _) =>
              aliasHeld := aliasHeld + 1
              checkM state s!"{lbl} fuel {m}: parseNode_alias_progress" (ps.pos < ps'.pos)
                s!"pos {ps.pos} → {ps'.pos}"
            | _ => aliasFail := aliasFail + 1
            if 2 < m && ps'.pos == ps.pos then
              deadHeld := deadHeld + 1
              let t := L4YAML.Proofs.Serialization.ParseCheckFrom.tok arr ps.pos
              let notProp := match t with
                | some (.anchor _) => false
                | some (.tag _ _) => false
                | _ => true
              let concl := (pcf t && notProp) ||
                (t == some YamlToken.blockEntry && 0 < ps.pos && L4YAML.Proofs.Serialization.ParseCheckFrom.tok arr (ps.pos - 1) == some YamlToken.blockEntry)
              checkM state s!"{lbl} fuel {m}: parseNode_dead" concl s!"tok {repr t}"
            else deadFail := deadFail + 1
  checkM state s!"P92(v) parseNodeProperties_progress held={propHeld} failed={propFail} (no progress under the withdrawn premise={propCtrl}); parseNode_alias_progress held={aliasHeld} failed={aliasFail}; parseNode_dead held={deadHeld} failed={deadFail}"
    (propHeld > 0 && propCtrl > 0 && aliasHeld > 0 && deadHeld > 0 && deadFail > 0) ""

/-! **Priority 93 — S3 (β2a), the three scanner prerequisites of the `Shape` loop invariant,
    instantiated BEFORE the proofs (Rule 2).**  (1) `FlowSync s := s.flowLevel = s.flowStack.size ∧
    s.simpleKeyStack.size = s.flowStack.size` holds on every state `scanNextToken` reaches from
    `mk'` (the clauses of `ScannerState.WellFormed` that have primitive lemmas but no step / loop
    lemma); (2) `skipToContent` never clears `simpleKeyAllowed` (its only write is `:= true` at a
    line break); (3) a step taken in flow context leaves `indents` unchanged.  Predictions: P1 —
    FlowSync on every step of every row, 0 violations; P2 — 0 in-flow steps change `indents`, and
    block steps DO change them on `a: [b]` / `- [a]` (the premise is load-bearing); P3 —
    `skipToContent` keeps `allowed = true` on every state, and turns `false` into `true` on some
    (a newline ahead), so the fact is monotonicity, not constancy; P4 — `scanLoopFull` at fuel 0
    fails on every row, and every success at fuel 1..3 satisfies FlowSync. -/
namespace P93

def flowSync (s : ScannerState) : Bool :=
  s.flowLevel == s.flowStack.size && s.simpleKeyStack.size == s.flowStack.size

def indentsKey (s : ScannerState) : Array (Int × Bool) :=
  s.indents.map fun e => (e.column, e.isSequence)

def rows : List String :=
  [ "", "a", "[a]", "[a, b]", "[[a]]", "[[[a]]]", "{a: b}", "{a: [b, {c: d}]}", "[a: b]", "[? a : b]",
    "[a: b, c: d]", "- [a]", "- {a: b}", "a: [b]", "a:\n  - [b, c]\n  - {d: e}", "[a]: b", "{a: b}: c",
    "[\n  a,\n  b\n]", "{\n  a: b\n}", "[a\n, b]", "- a\n- [b]\n- c", "? [a]\n: b",
    "[a, [b, c], {d: [e]}]", "[&x a, *x]", "[!t a]", "[a]\n...\n[b]", "--- [a]\n--- {b: c}",
    "[a: b: c]", "[-a]", "[- a]", "[a\n  : b]", "a: b\n[c]", "\"[\"", "'['", "[']']", "[a #c\n]",
    "[a,]", "{a,}", "[,]", "]", "[", "{a: }", "[a]]", "- - [a]", "a:\n  b: [c]\n  d: {e: f}",
    "[a]\n- b", "[a]\n: b", "[\"a\": b]", "[a, b]: c", "{[a]: b}" ]

/-- all states `scanNextToken` reaches from the start state, in order (the start state first) -/
def trajectory (input : String) (max : Nat := 64) : List ScannerState := Id.run do
  let s0 := (ScannerState.mk' input).emit .streamStart
  let s0 := match s0.peek? with | some '\uFEFF' => s0.consumeBOM | _ => s0
  let mut acc := [s0]
  let mut cur := s0
  for _ in List.range max do
    match scanNextToken cur with
    | .ok (some s') => acc := s' :: acc; cur := s'
    | _ => break
  return acc.reverse

end P93

def testFlowSyncPrereqs (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 93: S3 (β2a) — FlowSync over scanNextToken, skipToContent keeps simpleKeyAllowed, indents frozen in flow"
  let mut steps := 0
  let mut flowSteps := 0
  let mut blockIndentChanges := 0
  let mut allowedKept := 0
  let mut allowedRaised := 0
  let mut deepest := 0
  let mut loopFuel0 := 0
  let mut loopFuelOut := 0
  let mut loopOk := 0
  let mut loopRefused := 0
  for input in P93.rows do
    let tr := P93.trajectory input
    checkM state s!"P93 {repr input}: start state FlowSync" (P93.flowSync tr.head!) ""
    let mut prev := tr.head!
    for s' in tr.tail! do
      steps := steps + 1
      deepest := max deepest s'.flowLevel
      checkM state s!"P93 {repr input} step {steps}: FlowSync (fl={s'.flowLevel} fs={s'.flowStack.size} sk={s'.simpleKeyStack.size})"
        (P93.flowSync s') ""
      if prev.inFlow then
        flowSteps := flowSteps + 1
        checkM state s!"P93 {repr input} step {steps}: in flow ⇒ indents unchanged"
          (P93.indentsKey s' == P93.indentsKey prev) s!"{repr (P93.indentsKey prev)} → {repr (P93.indentsKey s')}"
      else if P93.indentsKey s' != P93.indentsKey prev then
        blockIndentChanges := blockIndentChanges + 1
      prev := s'
    -- (2) skipToContent on every reached state, with the flag forced true and as it is
    for s in tr do
      match skipToContent { s with simpleKeyAllowed := true } with
      | .ok s'' =>
        allowedKept := allowedKept + 1
        checkM state s!"P93 {repr input} offset {s.offset}: skipToContent keeps simpleKeyAllowed = true"
          (s''.simpleKeyAllowed == true) ""
      | .error _ => pure ()
      if !s.simpleKeyAllowed then
        match skipToContent s with
        | .ok s'' => if s''.simpleKeyAllowed then allowedRaised := allowedRaised + 1
        | .error _ => pure ()
    -- (4) scanLoopFull at fuel 0..3 from the start state
    let s0 := tr.head!
    for fuel in List.range 4 do
      match scanLoopFull s0 fuel with
      | .error e =>
        if fuel == 0 then loopFuel0 := loopFuel0 + 1
        else match e with
          | .fuelExhausted _ _ => loopFuelOut := loopFuelOut + 1
          | _ => loopRefused := loopRefused + 1
      | .ok sF =>
        loopOk := loopOk + 1
        checkM state s!"P93 {repr input} scanLoopFull fuel {fuel}: success ⇒ FlowSync (fuel 0 never succeeds)"
          (fuel != 0 && P93.flowSync sF) ""
  checkM state s!"P93 steps={steps} in-flow steps={flowSteps} block steps changing indents={blockIndentChanges} skipToContent kept={allowedKept} raised={allowedRaised} deepest flow={deepest}"
    (steps > 0 && flowSteps > 0 && blockIndentChanges > 0 && allowedKept > 0 && allowedRaised > 0 && deepest >= 3) ""
  -- every row fails at fuel 0 (one error per row, never a success); fuel 1..3 splits into successes
  -- (short rows), `fuelExhausted` fuel-outs and scanner refusals (`]` → `flowEndOutsideFlow`), tallied apart
  checkM state s!"P93 scanLoopFull: fuel-0 failures={loopFuel0} rows={P93.rows.length} fuel 1..3 successes={loopOk} fuel-outs (`fuelExhausted`)={loopFuelOut} scanner refusals={loopRefused}"
    (loopFuel0 == P93.rows.length && loopOk > 0 && loopFuelOut > 0 && loopRefused > 0) ""
  -- withdrawn-premise control for `FlowSync_scanNextToken`: desynchronise the stacks of a reached
  -- state and step — the conclusion must FAIL somewhere, else the premise is idle
  let mut desyncBroken := 0
  let mut desyncStepped := 0
  for input in ["[a, b]", "{a: [b]}", "- [a]", "a: b"] do
    for s in P93.trajectory input do
      let bad := { s with flowStack := s.flowStack.push true }
      match scanNextToken bad with
      | .ok (some s') =>
        desyncStepped := desyncStepped + 1
        if !P93.flowSync s' then desyncBroken := desyncBroken + 1
      | _ => pure ()
  checkM state s!"P93 withdrawn FlowSync premise: stepped={desyncStepped} conclusion fails on {desyncBroken}"
    (desyncStepped > 0 && desyncBroken > 0) ""

/-! **Priority 94 — S3 (β2b), the `LiveInv` carrier of the `Shape` loop invariant, instantiated
    BEFORE the proofs (Rule 2).**  Seven clauses on every state `scanNextToken` reaches from `mk'`:
    head (`vals[0] = SS`), `Shape (vals s)`, deep (`1 < indents.size ∨ 0 ≤ currentIndent ⇒` the
    last real token is not a boundary), flow (`0 < flowLevel ⇒` same), fresh (boundary ⇒
    `currentIndent = −1 ∧ flowLevel = 0`), slot (`simpleKey.possible ⇒` the token before the slot
    is not a boundary, or `flowLevel = 0 ∧ (currentIndent < key.col ∨ (simpleKeyAllowed ∧` the indent top is
    the sequence entry at the key's column`))`), stack
    (`∀ j`, a possible stacked key's predecessor is not a boundary, or `j = 0 ∧ currentIndent <
    key.col`), tail / stackTail (no boundary token from a possible key's slot onwards — what makes the
    inserted `.key`'s `.value` live).  Predictions: P1 — all nine hold on every reached state of every row; P2 — the slot
    clause's `simpleKeyAllowed` alternative is LOAD-BEARING: with it withdrawn the clause fails on
    `- a` right after `scanBlockEntry` (the key saved at `-` sits after `SS`, `pushSequenceIndent`
    raised the indent and kept it); P3 — the stack clause's `j = 0` alternative is load-bearing:
    `[a]: b` pushes a key that sits right after `SS`. -/
namespace P94
open L4YAML.Proofs.DirectiveRuns (vals)

def bndAt (L : List YamlToken) (idx : Nat) : Bool := L4YAML.Proofs.DocStartLive.Bnd (L4YAML.Proofs.DocStartLive.lastReal (L.take idx))

/-- v3 of the slot arm: the stale key a `-` leaves behind is recognisable — `simpleKeyAllowed`
    is still up AND the indent top is the sequence entry at the key's column (which is exactly
    what `scanValueValidate` refuses with `trailingContent`). -/
def seqTopAt (s : ScannerState) (k : SimpleKeyState) : Bool :=
  match s.indents.back? with
  | some top => top.isSequence && top.column == (k.pos.col : Int)
  | none => false

def slotOK (s : ScannerState) (allowedArm : Bool) : Bool :=
  !s.simpleKey.possible ||
    !bndAt (vals s) s.simpleKey.tokenIndex ||
    (s.flowLevel == 0 && (s.currentIndent < (s.simpleKey.pos.col : Int) ||
      (allowedArm && s.simpleKeyAllowed && seqTopAt s s.simpleKey)))

def tailOK (L : List YamlToken) (idx : Nat) : Bool :=
  (L.drop idx).all fun t => !L4YAML.Proofs.DocStartLive.Bnd (some t)

def stackTailOK (s : ScannerState) : Bool :=
  s.simpleKeyStack.all fun k => !k.possible || tailOK (vals s) k.tokenIndex

def stackOK (s : ScannerState) (zeroArm : Bool) : Bool :=
  (List.range s.simpleKeyStack.size).all fun j =>
    match s.simpleKeyStack[j]? with
    | some k => !k.possible || !bndAt (vals s) k.tokenIndex ||
        (zeroArm && j == 0 && s.currentIndent < (k.pos.col : Int))
    | none => true

def clauses (s : ScannerState) : List (String × Bool) :=
  let L := vals s
  let b := L4YAML.Proofs.DocStartLive.Bnd (L4YAML.Proofs.DocStartLive.lastReal L)
  [ ("head", L[0]? == some .streamStart),
    ("shape", P92.shapeB L),
    ("deep", !(1 < s.indents.size || 0 ≤ s.currentIndent) || !b),
    ("flow", !(0 < s.flowLevel) || !b),
    ("fresh", !b || (s.currentIndent == -1 && s.flowLevel == 0)),
    ("slot", slotOK s true),
    ("stack", stackOK s true),
    ("tail", !s.simpleKey.possible || tailOK L s.simpleKey.tokenIndex),
    ("stackTail", stackTailOK s) ]

def rows : List String :=
  P91.rows ++ P92.extraRows ++ P93.rows ++
  [ "- a", "- :b", "- - a", "-\n- a", "- a: b", "- [a]: b", "[a]: b", "{a: b}: c", "? a\n: b",
    "? - a\n: b", "a:\n  - b\n  c: d", "a:\n- b", "- a\n  b: c", "[a, b]: c\nd: e", "&x a: b",
    "!t a: b", "\"a\": b", "'a': b", "a: b\n...\n- c", "...\n- a", "---\n- a", "--- - a",
    "--- a: b", "...\na: b", "[\n  a: b\n]", "{a: [b: c]}", "[a]\n: b", "a\n: b" ]
end P94

def testLiveInvCarrier (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 94: S3 (β2b) — the LiveInv carrier on every reached scanner state"
  let mut states := 0
  let mut slotNoAllowed := 0
  let mut stackNoZero := 0
  let mut seqTopStale := 0
  let mut keyStates := 0
  let mut stackStates := 0
  for input in P94.rows do
    let mut k := 0
    for s in P93.trajectory input do
      states := states + 1
      for (nm, ok) in P94.clauses s do
        checkM state s!"P94 {repr input} state {k}: {nm}" ok
          s!"vals={repr (L4YAML.Proofs.DirectiveRuns.vals s)} ci={s.currentIndent} fl={s.flowLevel} ind={s.indents.size} key={s.simpleKey.possible}/{s.simpleKey.tokenIndex}/{s.simpleKey.pos.col} allowed={s.simpleKeyAllowed}"
      if s.simpleKey.possible then keyStates := keyStates + 1
      if s.simpleKeyStack.any (·.possible) then stackStates := stackStates + 1
      if !P94.slotOK s false then slotNoAllowed := slotNoAllowed + 1
      if !P94.stackOK s false then stackNoZero := stackNoZero + 1
      if s.simpleKey.possible && P94.bndAt (L4YAML.Proofs.DirectiveRuns.vals s) s.simpleKey.tokenIndex
          && !(s.currentIndent < (s.simpleKey.pos.col : Int)) then seqTopStale := seqTopStale + 1
      k := k + 1
  checkM state s!"P94 states={states} rows={P94.rows.length} key-possible states={keyStates} stacked-key states={stackStates}; withdrawn `simpleKeyAllowed` arm fails on {slotNoAllowed}; withdrawn `j = 0` arm fails on {stackNoZero}; stale-after-`-` keys (boundary before the slot, indent not below the key) = {seqTopStale}"
    (states > 0 && keyStates > 0 && stackStates > 0 && slotNoAllowed > 0 && stackNoZero > 0 && seqTopStale > 0) ""

namespace P94
open L4YAML.Proofs.Serialization.ParseCheckFrom (tok)

/-- `LoopDead ts k`, computed. -/
def loopDeadB (ts : Array (Positioned YamlToken)) (k : Nat) : Bool :=
  (P92.deadTok (tok ts k) || (tok ts k == some .blockEntry && decide (0 < k) &&
      tok ts (k - 1) == some .blockEntry)) &&
    tok ts k != some .documentEnd &&
    (k == 1 || tok ts (k - 1) == some .documentEnd || P91.afterDocOK (tok ts k))

/-- `DeadResidue (tok ts k)`, computed: the `.afterDocument` shape (the `.comment` disjunct was
closed by `scanFiltered_noComment`, Priority 96). -/
def residueB (ts : Array (Positioned YamlToken)) (k : Nat) : Bool :=
  P91.afterDocOK (tok ts k)

/-- `LoopDead_scanFiltered`'s conclusion. -/
def dischargeB (ts : Array (Positioned YamlToken)) (k : Nat) : Bool :=
  k == ts.size || tok ts k == some .streamEnd || residueB ts k

def alphabet : List YamlToken :=
  [.streamStart, .documentEnd, .documentStart, .key, .value, .blockEnd, .flowEntry,
   .flowSequenceEnd, .scalar "a" .plain, .blockEntry, .blockMappingStart, .streamEnd]

def listsUpTo : Nat → List (List YamlToken)
  | 0 => [[]]
  | n + 1 => let r := listsUpTo n; r ++ (r.filter (·.length == n)).flatMap fun l => alphabet.map (l ++ [·])

/-- `liveF_dead_contra`'s position premise: `k = 1 ∨ L[k-1] = .documentEnd`. -/
def posB (L : List YamlToken) (k : Nat) : Bool := k == 1 || L[k - 1]? == some .documentEnd
end P94

def testLoopDeadDischarge (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 94 (vi): S3 (β2b) — scanFiltered_liveF, liveF_dead_contra, LoopDead_scanFiltered"
  -- (a) list level: with `LiveF` and `.streamStart` first, no dead token at 1 / after `...`
  let mut held := 0
  let mut failedPremise := 0
  let mut deadUnderFailed := 0
  for L in P94.listsUpTo 4 do
    if L[0]? != some .streamStart then continue
    let live := P92.liveFB L
    for k in List.range L.length do
      if k == 0 || !P94.posB L k then continue
      match L[k]? with
      | some t =>
        if live then
          held := held + 1
          checkM state s!"P94 (vi) liveF_dead_contra {repr L} k={k}" (L4YAML.Proofs.DocStartLive.liveTok t) ""
        else
          failedPremise := failedPremise + 1
          if !L4YAML.Proofs.DocStartLive.liveTok t then deadUnderFailed := deadUnderFailed + 1
      | none => pure ()
  checkM state s!"P94 (vi) liveF_dead_contra: premise-held rows={held}, failed-premise rows={failedPremise}, dead under failed premise={deadUnderFailed} (load-bearing)"
    (held > 0 && deadUnderFailed > 0) ""
  -- (b) scanner outputs: `LiveF` + head, and the discharge at every `LoopDead` position
  let mut scanned := 0
  let mut loopDeadPos := 0
  let mut atOne := 0
  let mut afterDE := 0
  for input in P94.rows do
    match scanFiltered input with
    | .error _ => pure ()
    | .ok ts =>
      scanned := scanned + 1
      let L := L4YAML.Proofs.DirectiveRuns.toks ts
      checkM state s!"P94 (vi) scanFiltered_liveF {repr input}: LiveF" (P92.liveFB L) s!"toks={repr L}"
      checkM state s!"P94 (vi) scanFiltered_liveF {repr input}: head" (L[0]? == some .streamStart) ""
      for k in List.range (ts.size + 1) do
        if P94.loopDeadB ts k then
          loopDeadPos := loopDeadPos + 1
          if k == 1 then atOne := atOne + 1
          if L4YAML.Proofs.Serialization.ParseCheckFrom.tok ts (k - 1) == some YamlToken.documentEnd then afterDE := afterDE + 1
          checkM state s!"P94 (vi) (β2b) discharge shape at a LoopDead position (mirror; the lemma `LoopDead_scanFiltered` is retired by (γ2α)) {repr input} k={k}" (P94.dischargeB ts k)
            s!"tok={repr (L4YAML.Proofs.Serialization.ParseCheckFrom.tok ts k)} toks={repr L}"
  -- (c) non-tautology on hand-altered arrays (the `scanFiltered` premise is load-bearing):
  --     `.streamStart` at index 1 satisfies `LoopDead ts 1` and refutes the conclusion (dead, not in
  --     `validNextToken .afterDocument`); `.key` at index 1 also satisfies
  --     `LoopDead ts 1` but the conclusion is TRUE through `DeadResidue` — `.afterDocument` admits
  --     `.key`: that is (γ), the residue the item prices, pinned here as in P91's `a: b` row.
  match scanFiltered "- a" with
  | .ok ts0 =>
    let tsS := ts0.modify 1 fun p => { p with val := .streamStart }
    checkM state "P94 (vi) pin: LoopDead holds at 1 on [SS, SS, …]" (P94.loopDeadB tsS 1) ""
    checkM state "P94 (vi) pin: the discharge fails there (premise load-bearing)" (!P94.dischargeB tsS 1) ""
    let tsK := ts0.modify 1 fun p => { p with val := .key }
    checkM state "P94 (vi) pin: LoopDead holds at 1 on [SS, key, …]" (P94.loopDeadB tsK 1) ""
    checkM state "P94 (vi) pin: `.key` at 1 is TRUE under the (γ) residue shape (the loop now refuses it — (γ2α))" (P94.dischargeB tsK 1) ""
  | .error _ => checkM state "P94 (vi) pin: `- a` scans" false ""
  checkM state s!"P94 (vi) scanned={scanned} LoopDead positions={loopDeadPos} (k=1: {atOne}, after `...`: {afterDE})"
    (scanned > 0 && loopDeadPos > 0) ""

namespace P94
/-- `TailOK_set`'s conclusion on the written list, premise `Bnd (some t) = false`. -/
def tailSetB (L : List YamlToken) (idx j : Nat) (t : YamlToken) : Bool := tailOK (L.set j t) idx
/-- `Bnd_lastReal_set_false`'s conclusion. -/
def lastSetB (L : List YamlToken) (j : Nat) (t : YamlToken) : Bool :=
  !L4YAML.Proofs.DocStartLive.Bnd (L4YAML.Proofs.DocStartLive.lastReal (L.set j t))
/-- `Shape_set`'s side premise `hj`: a dead write lands after a non-boundary real token. -/
def hjB (L : List YamlToken) (j : Nat) (t : YamlToken) : Bool :=
  L4YAML.Proofs.DocStartLive.liveTok t ||
    !L4YAML.Proofs.DocStartLive.Bnd (L4YAML.Proofs.DocStartLive.lastReal (L.take j))
end P94

/-- Priority 94 (vii): the three token-rewrite lemmas `scanValue`'s retroactive insertion consumes,
    on every list of length ≤ 3 over the 12-token alphabet, every position `j ≤ length` (the
    out-of-range `j = length` row is the identity control) and every written token `t` — premises
    computed, conclusions checked where they hold (a violation is its own named row; the tally
    asserts there are none), failed-premise rows tallied apart with the count
    of rows where the conclusion also fails (the premise is load-bearing), and the withdrawn-`hj`
    control for `Shape_set`. -/
def testSetLemmas (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 94 (vii): S3 (β2b) — TailOK_set, Bnd_lastReal_set_false, Shape_set"
  let mut tailHeld := 0
  let mut tailViol := 0
  let mut lastViol := 0
  let mut shapeViol := 0
  let mut tailFailed := 0
  let mut tailFailedBroken := 0
  let mut lastHeld := 0
  let mut lastFailed := 0
  let mut lastFailedBroken := 0
  let mut shapeHeld := 0
  let mut shapeFailed := 0
  let mut shapeFailedBroken := 0
  let mut hjWithdrawnBroken := 0
  for L in P94.listsUpTo 3 do
    let shL := P92.shapeB L
    let lastL := !L4YAML.Proofs.DocStartLive.Bnd (L4YAML.Proofs.DocStartLive.lastReal L)
    for j in List.range (L.length + 1) do
      for t in P94.alphabet do
        let tb := !L4YAML.Proofs.DocStartLive.Bnd (some t)
        let np := L4YAML.Proofs.DirectiveRuns.nonPh t
        let W := L.set j t
        -- TailOK_set: ∀ idx ≤ length
        for idx in List.range (L.length + 1) do
          if tb && P94.tailOK L idx then
            tailHeld := tailHeld + 1
            if !P94.tailSetB L idx j t then
              tailViol := tailViol + 1
              checkM state s!"P94 (vii) TailOK_set {repr L} idx={idx} j={j} t={repr t}" false ""
          else
            tailFailed := tailFailed + 1
            if !P94.tailSetB L idx j t then tailFailedBroken := tailFailedBroken + 1
        -- Bnd_lastReal_set_false
        if np && tb && lastL then
          lastHeld := lastHeld + 1
          if !P94.lastSetB L j t then
            lastViol := lastViol + 1
            checkM state s!"P94 (vii) Bnd_lastReal_set_false {repr L} j={j} t={repr t}" false ""
        else
          lastFailed := lastFailed + 1
          if !P94.lastSetB L j t then lastFailedBroken := lastFailedBroken + 1
        -- Shape_set, and the withdrawn-`hj` control
        if np && tb && shL then
          if P94.hjB L j t then
            shapeHeld := shapeHeld + 1
            if !P92.shapeB W then
              shapeViol := shapeViol + 1
              checkM state s!"P94 (vii) Shape_set {repr L} j={j} t={repr t}" false ""
          else
            shapeFailed := shapeFailed + 1
            if !P92.shapeB W then
              shapeFailedBroken := shapeFailedBroken + 1
              hjWithdrawnBroken := hjWithdrawnBroken + 1
        else
          shapeFailed := shapeFailed + 1
          if !P92.shapeB W then shapeFailedBroken := shapeFailedBroken + 1
  checkM state s!"P94 (vii) TailOK_set: premise-held rows={tailHeld} (violations {tailViol}), failed-premise rows={tailFailed}, conclusion false under failed premise={tailFailedBroken} (load-bearing)"
    (tailHeld > 0 && tailViol == 0 && tailFailedBroken > 0) ""
  checkM state s!"P94 (vii) Bnd_lastReal_set_false: premise-held rows={lastHeld} (violations {lastViol}), failed-premise rows={lastFailed}, conclusion false under failed premise={lastFailedBroken} (load-bearing)"
    (lastHeld > 0 && lastViol == 0 && lastFailedBroken > 0) ""
  checkM state s!"P94 (vii) Shape_set: premise-held rows={shapeHeld} (violations {shapeViol}), failed-premise rows={shapeFailed}, conclusion false under failed premise={shapeFailedBroken} (load-bearing)"
    (shapeHeld > 0 && shapeViol == 0 && shapeFailedBroken > 0) ""
  checkM state s!"P94 (vii) Shape_set: withdrawn-`hj` control — `Shape L`, non-boundary dead `t` written after a boundary, `Shape` lost on {hjWithdrawnBroken} rows"
    (hjWithdrawnBroken > 0) ""
  -- pins: `[SS, a]` with `.key` written at 1 keeps `Shape` only through `hj`'s failure, i.e. it is lost
  let L : List YamlToken := [.streamStart, .scalar "a" .plain]
  checkM state "P94 (vii) pin: `Shape [SS, a]`" (P92.shapeB L) ""
  checkM state "P94 (vii) pin: writing `.key` at 1 of `[SS, a]` fails `hj` (last real before 1 is `SS`)" (!P94.hjB L 1 .key) ""
  checkM state "P94 (vii) pin: and `Shape` is lost there (the `hj` premise is load-bearing)" (!P92.shapeB (L.set 1 .key)) ""
  checkM state "P94 (vii) pin: writing `.key` at 2 of `[SS, a, b]` keeps `Shape`" (P92.shapeB ([.streamStart, .scalar "a" .plain, .scalar "b" .plain].set 2 .key)) ""

/-! ## Priority 95: S3 (a) — every `.tag` the scanner emits has a shaped handle (`TagUsesShaped`)

Statement under test (before the proof, Rule 2): `scanFiltered input = .ok ts → TagUsesShaped ts`,
i.e. every `.tag h _` in `ts` has `h ∈ {"", "!", "!!"}` or `isNamedHandle h`.  The proof route is a
per-token invariant `TagInv s := ∀ t ∈ vals s, tagOk t` carried over `scanNextToken` through
`TagExt s s' := ∀ t ∈ vals s', t ∈ vals s ∨ tagOk t`; the only arm that builds a `.tag` is
`scanTag` (`scanNamedTag` emits `"!" ++ w ++ "!"` with `w` all `ns-word-char`, or `"!"`), so the
load-bearing facts are (1) `isWordCharBool c → c.isAlphanum ∨ c = '-'` and (2) no other arm
emits a `.tag`.  Grid: every handle shape at first/middle/last position, block and flow, `%TAG`
directive handles (shaped and refused), the empty / blank / comment-only inputs, the per-step `TagExt`/`TagInv` on every reached state,
`scanLoop` direct at fuel 0/1/2, the word-char agreement on all ASCII, the scanner's
`isTagHandleShaped` against the parser's `isNamedHandle` on every handle ≤ 5 over a six-char
alphabet, and a withdrawn-`TagInv` control (a bad tag already in `vals` is carried, not repaired). -/

namespace P95

/-- `tagOk`, computed: the token-level form of `TagUsesShaped`. -/
def tagOkB : YamlToken → Bool
  | .tag h _ => h == "" || h == "!" || h == "!!" || L4YAML.Proofs.Serialization.TokenEvents.isNamedHandle h
  | .comment _ => false
  | _ => true

def tagInvB (s : ScannerState) : Bool := (L4YAML.Proofs.DirectiveRuns.vals s).all tagOkB

def tagExtB (s s' : ScannerState) : Bool :=
  (L4YAML.Proofs.DirectiveRuns.vals s').all fun t => (L4YAML.Proofs.DirectiveRuns.vals s).contains t || tagOkB t

def handleOf : YamlToken → Option String
  | .tag h _ => some h
  | _ => none

def rows : List String :=
  [ "", " ", "\n", "#c", "!t a", "! a", "!", "!!str a", "!!", "!e!x a", "!e! a", "!e-1!x a", "!1!x a", "!-!x a", "!--!x a",
    "!abcdefghijklmnopqrstuvwxyz0123456789-!x a", "!e_1!x a", "!é!x a", "!a!b!c", "!a!!b", "!!!a",
    "!<tag:x> a", "!<tag:x>!y a", "!<> a", "!<tag:x a", "!a!\tb", "!a!", "! !", "!! !!",
    "[!e!x a, !!int 1, !<tag:u> b]", "{!t a: !t b}", "? !t a\n: !t b", "- !t a\n- !!str b",
    "!t\n- a", "--- !t\na", "!t a: b", "a: !t b", "&x !t a", "!t &x a", "*x !t", "!t *x",
    "!t \"a\"", "!t 'a'", "!t |\n a", "!t >\n a", "!!binary |\n AAAA", "[!a!]", "!a!]", "!a!}",
    "[!a!,b]", "\uFEFF!t a", "--- !!map\na: b", "...\n!t a", "%YAML 1.2\n--- !t a", "#c\n!t a",
    "%TAG !e! tag:x\n--- !e!y a", "%TAG ! tag:x\n--- !y a", "%TAG !! tag:x\n--- !!y a",
    "%TAG !e! tag:x\n---\n!e!y a\n...\n%TAG !f! tag:y\n--- !f!z b", "!e!y a\n...\n%TAG !e! tag:x\n--- !e!z b",
    "%TAG !e tag:x\n--- a", "%TAG e! tag:x\n--- a", "%TAG !e_1! tag:x\n--- a", "%TAG !é! tag:x\n--- a",
    "%TAG !! tag:x\n%TAG !! tag:y\n--- a", "%TAG !e! tag:x\n--- !e!y a\n--- !e!z b",
    "a: [b, !t c]\nd: !!str e", "- - !t a\n  - !!int 1\n- !e!x b" ]

/-- The scanner's directive-side handle predicate. -/
def shapedScanner (h : String) : Bool := L4YAML.Scanner.isTagHandleShaped h

/-- The parser-side predicate (`BuiltinTagHandle ∨ isNamedHandle`), restricted to `h ≠ ""`. -/
def shapedParser (h : String) : Bool :=
  h == "!" || h == "!!" || L4YAML.Proofs.Serialization.TokenEvents.isNamedHandle h

def handleAlphabet : List Char := ['!', 'a', '1', '-', '_', ' ']

def handlesUpTo : Nat → List String
  | 0 => [""]
  | n + 1 => let r := handlesUpTo n; r ++ (r.filter (·.length == n)).flatMap fun h => handleAlphabet.map (h.push ·)

end P95

def testTagUsesShaped (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 95: S3 (a) — every scanner-emitted `.tag` has a shaped handle (TagUsesShaped)"
  let mut scanned := 0
  let mut refused := 0
  let mut refusedHandle := 0
  let mut tags := 0
  let mut verbatim := 0
  let mut primary := 0
  let mut secondary := 0
  let mut named := 0
  let mut steps := 0
  let mut states := 0
  for input in P95.rows do
    match L4YAML.Scanner.scanFiltered input with
    | .ok ts =>
      scanned := scanned + 1
      checkM state s!"P95 {repr input}: TagUsesShaped on scanner output" (s5TagUsesShaped ts)
        s!"tokens={repr (ts.map (·.val))}"
      for p in ts do
        match P95.handleOf p.val with
        | some h =>
          tags := tags + 1
          if h == "" then verbatim := verbatim + 1
          else if h == "!" then primary := primary + 1
          else if h == "!!" then secondary := secondary + 1
          else named := named + 1
        | none => pure ()
    | .error e =>
      refused := refused + 1
      match e with
      | .invalidTagHandle .. => refusedHandle := refusedHandle + 1
      | _ => pure ()
    -- per step: TagInv on every reached state, TagExt across every step
    let traj := P93.trajectory input
    let mut prev : Option ScannerState := none
    for s in traj do
      states := states + 1
      checkM state s!"P95 {repr input}: TagInv on reached state {states}" (P95.tagInvB s)
        s!"vals={repr (L4YAML.Proofs.DirectiveRuns.vals s)}"
      match prev with
      | some s0 =>
        steps := steps + 1
        checkM state s!"P95 {repr input}: TagExt across step {steps}" (P95.tagExtB s0 s) ""
      | none => pure ()
      prev := some s
    -- scanLoop direct from the start state at fuel 0 / 1 / 2 / enough
    let s0 := (ScannerState.mk' input).emit .streamStart
    checkM state s!"P95 {repr input}: scanLoop fuel 0 fails" (match L4YAML.Scanner.scanLoop s0 0 with | .ok _ => false | .error _ => true) ""
    for fuel in [1, 2, 64] do
      match L4YAML.Scanner.scanLoop s0 fuel with
      | .ok ts => checkM state s!"P95 {repr input}: scanLoop fuel {fuel} output TagUsesShaped" (s5TagUsesShaped ts) ""
      | .error _ => pure ()
  checkM state s!"P95 rows={P95.rows.length} scanned={scanned} refused={refused} (invalidTagHandle {refusedHandle}); tags={tags}: verbatim {verbatim}, primary {primary}, secondary {secondary}, named {named}; states={states} steps={steps}"
    (scanned > 0 && refused > 0 && refusedHandle > 0 && verbatim > 0 && primary > 0 && secondary > 0 && named > 0 && steps > 0) ""
  -- (1) the word-char agreement the proof rests on, on every ASCII char and a few beyond
  let chars : List Char := (List.range 128).map Char.ofNat ++ ['é', 'É', '\u00A0', '–', '\uFEFF', '字']
  let disagree := chars.filter fun c => L4YAML.CharPredicates.isWordCharBool c != (c.isAlphanum || c == '-')
  checkM state s!"P95 isWordCharBool c = (c.isAlphanum || c = '-') on {chars.length} chars" disagree.isEmpty s!"disagree={repr disagree}"
  -- scanner's `isTagHandleShaped` vs parser's `BuiltinTagHandle ∨ isNamedHandle` on every handle ≤ 5
  let hs := P95.handlesUpTo 5
  let mism := hs.filter fun h => h != "" && P95.shapedScanner h != P95.shapedParser h
  let shapedCount := (hs.filter P95.shapedParser).length
  checkM state s!"P95 isTagHandleShaped = (builtin ∨ isNamedHandle) on {hs.length} handles ({shapedCount} shaped)"
    (mism.isEmpty && shapedCount > 3) s!"mismatch={repr mism}"
  checkM state "P95 pin: \"\" is builtin (verbatim) but not `isTagHandleShaped`"
    (!P95.shapedScanner "" && P95.tagOkB (.tag "" "tag:x")) ""
  -- non-tautology: hand-built bad tags fail the predicate
  checkM state "P95 pin: `.tag \"!bad\" \"\"` is NOT shaped" (!P95.tagOkB (.tag "!bad" "")) ""
  checkM state "P95 pin: `.tag \"!a_b!\" \"\"` is NOT shaped (`_` is not a word char)" (!P95.tagOkB (.tag "!a_b!" "")) ""
  checkM state "P95 pin: `.tag \"!a-b!\" \"x\"` IS shaped" (P95.tagOkB (.tag "!a-b!" "x")) ""
  checkM state "P95 pin: `s5TagUsesShaped` refutes an array holding `.tag \"!bad\" \"\"`"
    (!s5TagUsesShaped #[s5Tok .streamStart, s5Tok (.tag "!bad" ""), s5Tok .streamEnd]) ""
  -- withdrawn `TagInv` control: a bad tag already in `vals` is carried through a step, not repaired
  let sBad := ((ScannerState.mk' "a").emit .streamStart).emit (.tag "!bad" "")
  checkM state "P95 control: TagInv fails on the seeded state" (!P95.tagInvB sBad) ""
  match L4YAML.Scanner.scanNextToken sBad with
  | .ok (some s') =>
    checkM state "P95 control: the step is TagExt (nothing new is unshaped) …" (P95.tagExtB sBad s') ""
    checkM state "P95 control: … but TagInv still fails after it (the premise is load-bearing)" (!P95.tagInvB s') ""
  | _ => checkM state "P95 control: seeded state steps" false ""

/-! ## Priority 96: S3 — the scanner emits no `.comment` token (`DeadResidue` shrinks to (γ))

Statement under test: `scanFiltered input = .ok ts → tok ts k ≠ some (.comment text)`
(`ScannerShape.scanFiltered_noComment`, from `TagShape.emitOk (.comment _) = false` carried over
`scanLoop`).  Grid: comments at every position the syntax admits (after scalars, indicators,
anchors, tags, directives, document markers, inside flow, after block-scalar headers, comment-only
lines and documents, `#` that is NOT a comment — inside scalars and quoted strings), every P91–P95
row, per-step `emitOk` on every reached state, a hand-built refuter, and a seeded-`.comment`
control (carried, not repaired). -/

namespace P96

def rows : List String :=
  [ "#c", "# c", "#", "#c\n#d", "a # c", "a #c", "- a # c", "- # c\n  a", "a: b # c", "a: # c\n  b",
    "? a # c\n: b # d", "[a, # c\n b] # d", "{a: b, # c\n c: d}", "[ # c\n]", "\"a\" # c", "'a' # c",
    "|\n a\n# c", "| # c\n a", "> # c\n a\n# d", "&x # c\na", "!t # c\na", "*x # c", "&x a # c\n*x # d",
    "%YAML 1.2 # c\n---", "%TAG !e! tag:x # c\n--- !e!y a", "--- # c", "... # c", "--- # c\na\n... # d",
    "# c\n---\n# d\na\n# e\n...\n# f", "a#b", "a #b#c", "\"a # b\"", "'a # b'", "a: \"#b\"", "- -#", "#\ta",
    "\uFEFF# c\na", "a\n  # c\n  b", "a:\n  # c\n  b: c", "- a\n# c\n- b", "{a: b} # c", "[a] # c" ]

def noCommentB (ts : Array (Positioned YamlToken)) : Bool :=
  ts.all fun p => match p.val with | .comment _ => false | _ => true

end P96

def testNoComment (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 96: S3 — the scanner emits no `.comment` token (DeadResidue shrinks to the .afterDocument shape)"
  let mut scanned := 0
  let mut refused := 0
  let mut tokens := 0
  let mut states := 0
  let mut steps := 0
  let all := P96.rows ++ P95.rows ++ P94.rows ++ P91.rows
  for input in all do
    match L4YAML.Scanner.scanFiltered input with
    | .ok ts =>
      scanned := scanned + 1
      tokens := tokens + ts.size
      checkM state s!"P96 {repr input}: no `.comment` on scanner output" (P96.noCommentB ts)
        s!"tokens={repr (ts.map (·.val))}"
    | .error _ => refused := refused + 1
    let mut prev : Option ScannerState := none
    for s in P93.trajectory input do
      states := states + 1
      checkM state s!"P96 {repr input}: emitOk (no comment, shaped tags) on reached state {states}"
        ((L4YAML.Proofs.DirectiveRuns.vals s).all P95.tagOkB) s!"vals={repr (L4YAML.Proofs.DirectiveRuns.vals s)}"
      if let some s0 := prev then
        steps := steps + 1
        checkM state s!"P96 {repr input}: TagExt across step {steps}" (P95.tagExtB s0 s) ""
      prev := some s
  checkM state s!"P96 rows={all.length} (own {P96.rows.length}) scanned={scanned} refused={refused} tokens={tokens} states={states} steps={steps}"
    (scanned > 0 && tokens > 0 && steps > 0) ""
  -- non-tautology: a hand-built array holding a `.comment` fails the predicate and would satisfy
  -- the pre-item-451 `DeadResidue`; `LoopDead` holds there (a comment is `deadTok`)
  let bad := #[s5Tok .streamStart, s5Tok (.comment "c"), s5Tok .streamEnd]
  checkM state "P96 pin: `[SS, comment, SE]` fails `noCommentB`" (!P96.noCommentB bad) ""
  checkM state "P96 pin: `LoopDead` holds at 1 there (a comment is dead)" (P94.loopDeadB bad 1) ""
  -- finding: `validNextToken .afterDocument (.comment _) = true` — the `.afterDocument` shape
  -- already admitted a comment, so item 449's second disjunct was redundant and the shrink of
  -- `DeadResidue` is syntactic; the lemma's content is `scanFiltered_noComment` itself (the stop
  -- token is never a comment), which is what (γ)'s carrier may assume
  checkM state "P96 finding: `afterDocOK (.comment)` is TRUE (the old disjunct was redundant)"
    (P91.afterDocOK (some (.comment "c"))) ""
  checkM state "P96 pin: so the (β2b) discharge shape still holds on the hand-built array (through the shape; the lemma is retired by (γ2α))"
    (P94.dischargeB bad 1) ""
  -- control: a seeded `.comment` is carried through a step, not repaired
  let sBad := ((ScannerState.mk' "a").emit .streamStart).emit (.comment "c")
  match L4YAML.Scanner.scanNextToken sBad with
  | .ok (some s') =>
    checkM state "P96 control: the step is TagExt …" (P95.tagExtB sBad s') ""
    checkM state "P96 control: … and the seeded comment is still there (premise load-bearing)"
      (!(L4YAML.Proofs.DirectiveRuns.vals s').all P95.tagOkB) ""
  | _ => checkM state "P96 control: seeded state steps" false ""


namespace P97

/-- (γ1) depth step: block/flow openers +1, closers −1. -/
def depthStep : YamlToken → Int
  | .blockSequenceStart | .blockMappingStart | .flowSequenceStart | .flowMappingStart => 1
  | .blockEnd | .flowSequenceEnd | .flowMappingEnd => -1
  | _ => 0

def depth (L : List YamlToken) : Int := L.foldl (fun d t => d + depthStep t) 0

/-- The structural dead kinds `validNextToken .afterDocument` admits (DeadResidue minus the
boundary/`.comment`/`.placeholder` kinds already excluded). -/
def structDeadB : YamlToken → Bool
  | .key | .value | .blockEnd | .flowEntry | .flowSequenceEnd | .flowMappingEnd => true
  | _ => false

/-- `Bal L`: every structural dead token sits at positive depth. -/
def balB (L : List YamlToken) : Bool := Id.run do
  let mut d : Int := 0
  for t in L do
    if structDeadB t && !(0 < d) then return false
    d := d + depthStep t
  return true

def rows : List String :=
  [ "a", "a: b", ": b", ":", "? a", "? a\n: b", "? \n: ", "? a\n: b\n: c", "- a", "- - a", "- :", "- ? a",
    "- a\n- : b", "a:\n  b: c\n: d", "a:\n  ? b\n: c", "a:\n  b\n: c", "a: b\n: c", "[a]: b\n: c",
    "a:\n  - b\n: c", "a:\n  b:\n    c\nd: e", "a:\n  b:\n    c: d\n  e: f\ng: h", "[a]", "[a, b]", "[a: b]",
    "[: b]", "[a, : b]", "[a: b, c: d]", "{a}", "{a: b}", "{a: b, c}", "{a: b, c: d}", "[[a]]", "[[[a]]]",
    "[{a: [b, {c: d}]}]", "a: [b, {c: d}]", "- [a, b]\n- {c: d}", "[a]: b", "? [a]\n: b", "{a: b}: c",
    "? a\n...\n: b", "a: b\n...\n", "---\na: b\n---\n- c\n...", "--- a\n--- b", "...\n", "---\n...\n---",
    "|\n a\nb: c", ">\n a\n- b", "a: |\n  x\nb: c", "- |\n  x\n- y", "&x a: b", "!t a: b", "a: &x b\nc: *x",
    "\uFEFFa: b", "# c\na: b # d\n# e", "a:\n  # c\n  b: c\n# d\nd: e", "a:\n\n  b\n\nc: d",
    ", a", "]", "}", "a, b", "[a]b", "a: - b", "  ? a\n: b", "- ? a\n: b", "- a\n: b", "  a: b\n: c",
    "[a", "{a", "[a}", "{a]", "a: b: c", "[a, b,]", "{a: b,}", "[,]", "[a,,b]", "a:\n- b\n- c", "a:\nb: c",
    "- a:\n    b: c\n  d: e", "-\n  - a\n  - b", "? - a\n  - b\n: c", "? a: b\n: c", "[? a : b]", "{? a : b}",
    "a: \"b\": c", "\"a\": \"b\"", "'a': ['b']", "a: !!map {b: c}", "- !!seq [a]", "a:\n  -\n  - b" ]

def c1B (s : ScannerState) : Bool :=
  depth (L4YAML.Proofs.DirectiveRuns.vals s) == (s.indents.size : Int) - 1 + (s.flowLevel : Int)

def c3B (s : ScannerState) : Bool :=
  (s.indents[0]?.map (·.column) == some (-1)) &&
    (List.range s.indents.size).all (fun i => i == 0 || (s.indents[i]?.map (fun e => decide (0 ≤ e.column)) == some true))

/-- Prediction P4 (plain slot-tail neutrality) was REFUTED on `- a`: the key saved at `-` sits
before the `blockSequenceStart` that `pushSequenceIndent` emits.  Kept as the refuter's record. -/
def slotNeutralB (s : ScannerState) : Bool :=
  depth ((L4YAML.Proofs.DirectiveRuns.vals s).take (s.simpleKey.tokenIndex + 1)) ==
    depth (L4YAML.Proofs.DirectiveRuns.vals s)

/-- `DInv.slot` as proven (`DSlot`): the prefix through the slot's first placeholder is at positive
depth, or (block context) the key is stale-but-harmless — `SlotOK`'s alternative. -/
def c4B (s : ScannerState) : Bool :=
  !s.simpleKey.possible ||
    0 < depth ((L4YAML.Proofs.DirectiveRuns.vals s).take (s.simpleKey.tokenIndex + 1)) ||
    (s.flowLevel == 0 && (s.currentIndent < (s.simpleKey.pos.col : Int) || s.simpleKeyAllowed))

/-- `DInv.stack` as proven. -/
def c5B (s : ScannerState) : Bool :=
  (List.range s.simpleKeyStack.size).all fun j =>
    match s.simpleKeyStack[j]? with
    | some k => !k.possible ||
        0 < depth ((L4YAML.Proofs.DirectiveRuns.vals s).take (k.tokenIndex + 1)) ||
        (j == 0 && s.currentIndent < (k.pos.col : Int))
    | none => true

def phAtB (L : List YamlToken) (i : Nat) : Bool :=
  L[i]? == some .placeholder && L[i + 1]? == some .placeholder

/-- `DInv.ph` / `DInv.stackPh`: every saved slot still holds its two placeholders. -/
def c6B (s : ScannerState) : Bool :=
  let v := L4YAML.Proofs.DirectiveRuns.vals s
  (!s.simpleKey.possible || phAtB v s.simpleKey.tokenIndex) &&
    s.simpleKeyStack.all (fun k => !k.possible || phAtB v k.tokenIndex)

/-- `DInv.ordCur` / `DInv.ordStk`: saved slots are two apart and below the current one. -/
def c7B (s : ScannerState) : Bool :=
  let st := s.simpleKeyStack
  (!s.simpleKey.possible || st.all (fun k => !k.possible || k.tokenIndex + 2 ≤ s.simpleKey.tokenIndex)) &&
    (List.range st.size).all fun j => (List.range st.size).all fun j' =>
      match st[j]?, st[j']? with
      | some k, some k' => !(j < j') || !k.possible || !k'.possible || k.tokenIndex + 2 ≤ k'.tokenIndex
      | _, _ => true

end P97

def testGammaBal (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 97: S3 (γ1) — structural dead tokens sit at positive depth on scanner output (Bal)"
  let mut scanned := 0
  let mut refused := 0
  let mut tokens := 0
  let mut structural := 0
  let mut states := 0
  let mut slots := 0
  let mut slotsAlt := 0
  let mut stacked := 0
  let all := P97.rows ++ P96.rows ++ P95.rows ++ P94.rows ++ P91.rows
  for input in all do
    match L4YAML.Scanner.scanFiltered input with
    | .ok ts =>
      scanned := scanned + 1
      tokens := tokens + ts.size
      structural := structural + (ts.filter (fun p => P97.structDeadB p.val)).size
      checkM state s!"P97 {repr input}: Bal on scanner output" (P97.balB (ts.map (·.val)).toList)
        s!"tokens={repr (ts.map (·.val))}"
    | .error _ => refused := refused + 1
    for s in P93.trajectory input do
      states := states + 1
      let v := L4YAML.Proofs.DirectiveRuns.vals s
      checkM state s!"P97 {repr input}: c1 depth = indents.size - 1 + flowLevel on reached state {states}"
        (P97.c1B s) s!"depth={P97.depth v} indents={s.indents.size} fl={s.flowLevel} vals={repr v}"
      checkM state s!"P97 {repr input}: c3 indent stack sentinel/columns on reached state {states}" (P97.c3B s)
        s!"indents={repr (s.indents.map (·.column))}"
      checkM state s!"P97 {repr input}: c4 DSlot (slot prefix deep ∨ SlotOK alternative) on reached state {states}" (P97.c4B s)
        s!"idx={s.simpleKey.tokenIndex} vals={repr v}"
      checkM state s!"P97 {repr input}: c5 stacked slots (prefix deep ∨ j = 0 ∧ ci < col) on reached state {states}" (P97.c5B s)
        s!"stack={repr (s.simpleKeyStack.map (fun k => (k.possible, k.tokenIndex)))} fl={s.flowLevel} vals={repr v}"
      checkM state s!"P97 {repr input}: c6 saved slots hold two placeholders on reached state {states}" (P97.c6B s)
        s!"vals={repr v}"
      checkM state s!"P97 {repr input}: c7 slot ordering (two apart, stack below current) on reached state {states}" (P97.c7B s)
        s!"idx={s.simpleKey.tokenIndex} stack={repr (s.simpleKeyStack.map (fun k => (k.possible, k.tokenIndex)))}"
      checkM state s!"P97 {repr input}: Bal on reached raw state {states}" (P97.balB v) s!"vals={repr v}"
      if s.simpleKey.possible then
        slots := slots + 1
        if !P97.slotNeutralB s then slotsAlt := slotsAlt + 1
      stacked := stacked + (s.simpleKeyStack.filter (·.possible)).size
  checkM state s!"P97 rows={all.length} (own {P97.rows.length}) scanned={scanned} refused={refused} tokens={tokens} structural={structural} states={states} slots={slots} (non-neutral, via the SlotOK alternative: {slotsAlt}) stacked={stacked}"
    (scanned > 0 && structural > 0 && slots > 0 && slotsAlt > 0 && stacked > 0) ""
  -- scanLoop direct at fuel 0/1/2/64 from the initial state
  let mut loopOk := 0
  let mut loopFuelOut := 0
  for input in P97.rows do
    for fuel in [0, 1, 2, 64] do
      match L4YAML.Scanner.scanLoop ((ScannerState.mk' input).emit .streamStart) fuel with
      | .ok ts =>
        loopOk := loopOk + 1
        checkM state s!"P97 scanLoop {repr input} fuel={fuel}: Bal" (P97.balB (ts.map (·.val)).toList) ""
      | .error (.fuelExhausted ..) => loopFuelOut := loopFuelOut + 1
      | .error _ => pure ()
  checkM state s!"P97 scanLoop direct: ok={loopOk} fuelOut={loopFuelOut}" (loopOk > 0 && loopFuelOut > 0) ""
  -- refuters: hand-built arrays with a structural dead token at depth 0 fail Bal; balanced ones hold
  let SS := YamlToken.streamStart; let SE := YamlToken.streamEnd
  checkM state "P97 pin: [SS, key, SE] fails Bal" (!P97.balB [SS, .key, SE]) ""
  checkM state "P97 pin: [SS, value, SE] fails Bal" (!P97.balB [SS, .value, SE]) ""
  checkM state "P97 pin: [SS, bms, blockEnd, blockEnd, SE] fails Bal (second closer at depth 0)"
    (!P97.balB [SS, .blockMappingStart, .blockEnd, .blockEnd, SE]) ""
  checkM state "P97 pin: [SS, flowEntry, SE] fails Bal" (!P97.balB [SS, .flowEntry, SE]) ""
  checkM state "P97 pin: [SS, bms, key, value, blockEnd, SE] holds" (P97.balB [SS, .blockMappingStart, .key, .value, .blockEnd, SE]) ""
  checkM state "P97 pin: [SS, fss, flowEntry, fse, SE] holds" (P97.balB [SS, .flowSequenceStart, .flowEntry, .flowSequenceEnd, SE]) ""
  checkM state "P97 pin: a `.key` at depth 0 is `DeadResidue`-shaped (the (γ) residue; refused by the loop since (γ2α))"
    (P91.afterDocOK (some .key) && P94.loopDeadB #[s5Tok SS, s5Tok .documentEnd, s5Tok .key, s5Tok SE] 2) ""
  -- control: a seeded structural token at depth 0 is carried through a step, not repaired
  let sBad := ((ScannerState.mk' "a").emit .streamStart).emit .value
  match L4YAML.Scanner.scanNextToken sBad with
  | .ok (some s') =>
    checkM state "P97 control: seeded depth-0 `.value` survives the step (carried, not repaired)"
      (!P97.balB (L4YAML.Proofs.DirectiveRuns.vals s')) ""
  | _ => checkM state "P97 control: seeded state steps" false ""

namespace P98
open L4YAML.Proofs.Serialization.ParseCheckFrom (tok)

/-- (γ2) target measure: the net `P97.depth` of the tokens a parse consumed, `[i, j)`. -/
def depthSeg (ts : Array (Positioned YamlToken)) (i j : Nat) : Int :=
  P97.depth (((ts.toList.drop i).take (j - i)).map (·.val))

/-- `parseDocument`'s fuel (`4 * ts.size + 4`, inlined in the parser). -/
def docFuel (ts : Array (Positioned YamlToken)) : Nat := 4 * ts.size + 4

/-- Hand-built arrays for the parser's two leniencies: a block collection whose `blockEnd` is
missing (the loop exits at a foreign token and `parseBlock*` keeps the position), and fuel
running out inside a block loop (`parseBlock*Loop … 0 = .ok`).  `Bal` holds on every one of them
(the structural dead tokens sit after an opener), so the scanner side alone cannot exclude them. -/
def refuters : List (String × List YamlToken) :=
  let a := YamlToken.scalar "a" .plain
  let b := YamlToken.scalar "b" .plain
  [ ("[SS, bSS, bE, a, key, b, SE]", [.streamStart, .blockSequenceStart, .blockEntry, a, .key, b, .streamEnd]),
    ("[SS, bMS, key, a, value, b, flowEntry, SE]",
      [.streamStart, .blockMappingStart, .key, a, .value, b, .flowEntry, .streamEnd]),
    ("[SS, bSS, bE, a, value, SE]", [.streamStart, .blockSequenceStart, .blockEntry, a, .value, .streamEnd]),
    ("[SS, bMS, key, a, value, b, fSE, SE]",
      [.streamStart, .blockMappingStart, .key, a, .value, b, .flowSequenceEnd, .streamEnd]),
    ("[SS, bSS, bE, bSS, bE, a, bEnd, key, SE]",
      [.streamStart, .blockSequenceStart, .blockEntry, .blockSequenceStart, .blockEntry, a, .blockEnd, .key, .streamEnd]) ]

/-- Controls: balanced arrays (`parseNode` consumes through the closer) and the flow collections,
whose closer is not optional (`expectedToken`). -/
def controls : List (String × List YamlToken) :=
  let a := YamlToken.scalar "a" .plain
  [ ("[SS, bSS, bE, a, bEnd, SE]", [.streamStart, .blockSequenceStart, .blockEntry, a, .blockEnd, .streamEnd]),
    ("[SS, bMS, key, a, value, a, bEnd, SE]",
      [.streamStart, .blockMappingStart, .key, a, .value, a, .blockEnd, .streamEnd]),
    ("[SS, fSS, a, fSE, SE]", [.streamStart, .flowSequenceStart, a, .flowSequenceEnd, .streamEnd]),
    ("[SS, fMS, key, a, value, a, fME, SE]",
      [.streamStart, .flowMappingStart, .key, a, .value, a, .flowMappingEnd, .streamEnd]),
    ("[SS, fSS, a, key, SE] (flow: refused, not lenient)", [.streamStart, .flowSequenceStart, a, .key, .streamEnd]),
    ("[SS, fSS, a, bEnd, SE] (flow: refused, not lenient)", [.streamStart, .flowSequenceStart, a, .blockEnd, .streamEnd]) ]

end P98

def testGammaDepth (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 98: (γ2) — does parseNode / parseDocument consume a net-depth-0 segment?"
  -- (i) the NEXT's statement on arbitrary arrays: REFUTED by the block closers' leniency
  let mut refuted := 0
  for (nm, l) in P98.refuters do
    let arr := P91.mkArr l
    checkM state s!"P98(i) {nm}: Bal holds (the scanner side admits this array)" (P97.balB l) ""
    match parseNode (P91.at_ arr 1) (P98.docFuel arr) with
    | .ok (_, ps') =>
      let d := P98.depthSeg arr 1 ps'.pos
      if d != 0 then refuted := refuted + 1
      checkM state s!"P98(i) {nm}: parseNode from 1 succeeds at positive net depth (the missing `blockEnd` is tolerated)"
        (0 < d) s!"p'={ps'.pos} depth={d}"
    | .error _ => checkM state s!"P98(i) {nm}: parseNode from 1 succeeds" false ""
    -- the composed gap, before (γ2α): the shadow loop reaches the no-progress exit on the structural
    -- token at positive depth (a `DeadResidue` stop `Bal` admits); since (γ2α) the real loop refuses
    -- it as `trailingContent` at that token's position instead of returning `.ok`
    let sh := P91.shadow arr arr.size (P91.at_ arr 1) .initial []
    checkM state s!"P98(i) {nm}: the shadow loop's no-progress exit sits on a structural dead token at positive depth — the (γ) residue, reached"
      (sh.stuck && P97.structDeadB ((L4YAML.Proofs.Serialization.ParseCheckFrom.tok arr sh.stop).getD .streamEnd) && 0 < P98.depthSeg arr 0 sh.stop)
      s!"stuck={sh.stuck} stop={sh.stop} tok={repr (L4YAML.Proofs.Serialization.ParseCheckFrom.tok arr sh.stop)} depth={P98.depthSeg arr 0 sh.stop}"
    checkM state s!"P98(vi) {nm}: parseStream refuses it — `trailingContent` ((γ2α))"
      (P91.isTrailing (parseStream arr)) ""
    checkM state s!"P98(vi) {nm}: parseStreamMarkedLoop refuses it too"
      (P91.isTrailingM (L4YAML.Events.parseStreamMarkedLoop (P91.at_ arr 1) #[] .initial arr.size)) ""
  checkM state s!"P98(i) refuters={P98.refuters.length} net-depth≠0={refuted}: `depth (seg) = 0` for every successful parseNode is FALSE on arbitrary arrays (the (γ2) statement as priced in item 452)"
    (refuted == P98.refuters.length) ""
  for (nm, l) in P98.controls do
    let arr := P91.mkArr l
    match parseNode (P91.at_ arr 1) (P98.docFuel arr) with
    | .ok (_, ps') =>
      checkM state s!"P98(i) control {nm}: parseNode from 1 is balanced" (P98.depthSeg arr 1 ps'.pos == 0) s!"p'={ps'.pos}"
    | .error _ =>
      checkM state s!"P98(i) control {nm}: refused" (nm.endsWith "(flow: refused, not lenient)") ""
  -- (ii) the weaker claim that is true on arbitrary arrays: a successful parse never consumes more
  -- closers than openers (every consumed closer follows its own opener in the same call)
  let mut nodeRuns := 0
  let mut nonneg := 0
  let mut lowFuelPositive := 0
  let mut fullFuelZero := 0
  let mut fullFuelRuns := 0
  let all := P97.rows ++ P96.rows ++ P95.rows ++ P94.rows ++ P91.rows ++ P92.extraRows
  let mut scanned := 0
  let mut docSegs := 0
  let mut visited := 0
  let mut stuck := 0
  for input in all do
    match L4YAML.Scanner.scanFiltered input with
    | .error _ => pure ()
    | .ok ts =>
      scanned := scanned + 1
      for p in List.range ts.size do
        for fuel in [1, 2, 3, P98.docFuel ts] do
          match parseNode (P91.at_ ts p) fuel with
          | .error _ => pure ()
          | .ok (_, ps') =>
            nodeRuns := nodeRuns + 1
            let d := P98.depthSeg ts p ps'.pos
            if 0 ≤ d then nonneg := nonneg + 1
            if fuel == P98.docFuel ts then
              fullFuelRuns := fullFuelRuns + 1
              if d == 0 then fullFuelZero := fullFuelZero + 1
              checkM state s!"P98(iii) {repr input} parseNode from {p} at the parser's fuel: net depth 0"
                (d == 0) s!"p'={ps'.pos} depth={d} tokens={repr (ts.map (·.val))}"
            else if 0 < d then lowFuelPositive := lowFuelPositive + 1
      -- (iv) the loop's positions on scanner output sit at depth 0; no no-progress exit
      let sh := P91.shadow ts ts.size (P91.at_ ts 1) .initial []
      if sh.stuck then stuck := stuck + 1
      for q in sh.visited ++ [sh.stop] do
        visited := visited + 1
        checkM state s!"P98(iv) {repr input}: loop position {q} at depth 0" (P98.depthSeg ts 0 q == 0)
          s!"depth={P98.depthSeg ts 0 q} tokens={repr (ts.map (·.val))}"
      for q in sh.visited do
        match parseDocument (P91.at_ ts q) with
        | .ok (_, ps') =>
          docSegs := docSegs + 1
          checkM state s!"P98(iv) {repr input}: parseDocument segment from {q} has net depth 0"
            (P98.depthSeg ts q ps'.pos == 0) s!"p'={ps'.pos}"
        | .error _ => checkM state s!"P98(iv) {repr input}: parseDocument from visited {q} succeeds" false ""
  checkM state s!"P98(ii) parseNode runs on scanner output (every position, fuel 1/2/3/4n+4) = {nodeRuns}, net depth ≥ 0 on {nonneg} (all); low-fuel runs at positive depth (fuel-out leniency) = {lowFuelPositive}"
    (nodeRuns > 0 && nonneg == nodeRuns && lowFuelPositive > 0) ""
  checkM state s!"P98(iii) full-fuel runs = {fullFuelRuns}, net depth 0 on {fullFuelZero}" (fullFuelRuns > 0 && fullFuelZero == fullFuelRuns) ""
  checkM state s!"P98(iv) rows={all.length} scanned={scanned} loop positions={visited} document segments={docSegs} no-progress exits={stuck}"
    (scanned > 0 && visited > 0 && docSegs > 0 && stuck == 0) ""
  -- (v) fuel 0 / 1 / 2 / 4 on a balanced block sequence: fuel 0 and 1 are errors (the content
  -- dispatch gets fuel 0), fuel 2 leaves the loop at fuel 0 and the opener unclosed (lenient,
  -- depth 1), fuel 4 is the first that consumes the `blockEnd` — so the depth claim needs fuel
  -- adequacy even on conformant input.  (Prediction "fuel 1 lenient / fuel 3 balanced" was off by
  -- one: each loop iteration spends a fuel before the entry's `parseNode` gets its own.)
  let arr := P91.mkArr [.streamStart, .blockSequenceStart, .blockEntry, .scalar "a" .plain, .blockEnd, .streamEnd]
  let isErr : Except ScanError (YamlValue × ParseState) → Bool := fun r => match r with | .error _ => true | _ => false
  checkM state "P98(v) fuel 0: parseNode errors" (isErr (parseNode (P91.at_ arr 1) 0)) ""
  checkM state "P98(v) fuel 1: parseNode errors (parseBlockSequence at fuel 0)" (isErr (parseNode (P91.at_ arr 1) 1)) ""
  match parseNode (P91.at_ arr 1) 2 with
  | .ok (_, ps') => checkM state "P98(v) fuel 2 on [bSS, bE, a, bEnd]: the loop runs at fuel 0 and the opener stays unclosed (depth 1)"
      (P98.depthSeg arr 1 ps'.pos == 1) s!"p'={ps'.pos}"
  | .error _ => checkM state "P98(v) fuel 2 on [bSS, bE, a, bEnd] succeeds" false ""
  checkM state "P98(v) fuel 3: parseNode errors (the entry's parseNode gets fuel 0)" (isErr (parseNode (P91.at_ arr 1) 3)) ""
  match parseNode (P91.at_ arr 1) 4 with
  | .ok (_, ps') => checkM state "P98(v) fuel 4 on [bSS, bE, a, bEnd]: balanced" (P98.depthSeg arr 1 ps'.pos == 0) s!"p'={ps'.pos}"
  | .error _ => checkM state "P98(v) fuel 4 on [bSS, bE, a, bEnd] succeeds" false ""

/-! ## Priority 99: S3 proper — the surface bridge `scanFiltered input = .ok ts → TraceOf input (tokenEvents ts)`
(EVENTSOF §10 option 1), READ before any proof.  `TraceOf` is a `Prop` with no decision procedure, so the
executable mirror is the one the S2 census already uses: the scanner's trace `tokenEvents ∘ scanFiltered`
against the reference lexer's `eventsOf` (`refLex`, the executable twin of `Skeleton`).  The grid runs every
probe row of Priorities 91–97 plus boundary rows of its own (properties against flow/block indicators,
quoted/comment/block-scalar opacity, document markers, directives), tallies agreement per slice
(leaf / flow / block / documents), reads which token kinds the trace depends on (the consumer census of
items 446–452's scanner-shape facts), and reads the (β) `TokenGrammar` route's reach on the same rows.
Smallest term-level instances of the bridge itself: the empty stream (`traceOf_empty`, library), `---`,
`...`. -/
namespace P99
open L4YAML.Proofs.Serialization.EventsOf (refLex eventsOfSegs)
open L4YAML.Proofs.Serialization.TokenEvents (tokenEvents)
open L4YAML.Proofs.Serialization.SerializationWellFormed (Event checkFrom)
open L4YAML.Proofs.TokenGrammar (checkTokenGrammar)
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Surface

/-- Boundary rows of this priority: event lexemes against every neighbour the slices meet. -/
def own : List String :=
  [ -- leaf: a property or alias alone, and as a node's whole content
    "&x", "&x a", "*x", "!t a", "!!str a", "!<tag:x> a", "!e!a", "!t &x a", "&x !t a", "&x\n&y a",
    "&x *x", "!t *x", "&x a &y b",
    -- opacity: quoted scalars, comments, block scalars hold no event
    "a: \"&x\"", "a: '*x'", "'...'", "\"---\"", "# &x", "a # &x", "a: b # *x", "&x a # c",
    "a: |\n  &x\n", "a: >\n  *x\n  !t\n", "--- |\n &x", "&x |\n a", "? |\n  *x\n: b",
    -- flow: properties and aliases at every flow position
    "[&x a, *x]", "{&x a: *x}", "[a, &x b]", "[&x a]", "{a: &x b}", "&x [a]", "&x {a: b}",
    "[a # c\n, &x b]", "[*x]", "[&x a: *x]", "{&x a}", "[!t a, !!str b]", "[&x [*x]]", "{a: [&x b, *x]}",
    "[&x a,\n *x]", "[ &x a ]", "{ &x a : *x }",
    -- block: properties on keys, values, entries, explicit keys
    "- &x a\n- *x", "a: &x b\nc: *x", "? &x a\n: *x", "&x\n- a", "&x a: b", "&x a:\n  b", "- !t\n  &x a",
    "key: !t &x\n  - a", "a:\n  &x b: *x", "- &x\n  - a", "&x a\n&y b", "a: &x\nb: *x",
    -- document markers and directives: the `beginDocument`/`declareTag`/`endDocument` order
    "---", "...", "--- a", "a\n...", "---\n...\n---", "--- a\n...\n...", "...\n...", "\uFEFF--- a", "---a",
    "--- \n a", "a\n---\nb", "- ---", "a: ---", "--- &x a\n--- *x", "&x a\n...\n--- *x", "&x a\n--- *x",
    "%YAML 1.2\n--- a", "%TAG !e! tag:x\n--- !e!a", "%TAG !e! tag:x\n---\n!e!a",
    "%TAG !e! tag:x\n%TAG !f! tag:y\n--- !f!a", "%TAG !e! tag:x\n--- a\n--- !e!b",
    "%TAG !e! tag:x\n--- a\n...\n%TAG !f! tag:y\n--- !f!b", "%TAG ! !x\n--- !a", "%TAG !! tag:y\n--- !!str a",
    "%TAG !e! tag:x\n---\n...", "%TAG !e! tag:x", "--- !e!a\n%TAG !e! tag:x\n--- b",
    "[---]", "{...}", "a\n--- &x b\n--- *x", "---\n&x a\n---\n*x" ]

def allRows : List String :=
  (P91.rows ++ P93.rows ++ P94.rows ++ P95.rows ++ P96.rows ++ P97.rows ++ own).eraseDups

/-- (scanner trace, skeleton trace), each `none` where the reading refuses. -/
def both (s : String) : Option (List Event) × Option (List Event) :=
  ((scanFiltered s).toOption.map tokenEvents, (refLex s).map eventsOfSegs)

/-- The slice a row belongs to, by the outermost construct the SCANNER's tokens show (review of the
first cut: text-based labels counted `'...'`, `"---"`, `[---]` as documents).  A refused row has no
tokens and is labelled `refused`; the per-slice reading is over scanned rows only. -/
def sliceOf (s : String) : String :=
  match scanFiltered s with
  | .error _ => "refused"
  | .ok ts =>
    let ks := ts.toList.map (·.val)
    let isDoc : YamlToken → Bool
      | .documentStart | .documentEnd | .tagDirective .. | .versionDirective .. => true
      | _ => false
    let isFlow : YamlToken → Bool
      | .flowSequenceStart | .flowMappingStart => true
      | _ => false
    let isBlock : YamlToken → Bool
      | .blockSequenceStart | .blockMappingStart | .blockEntry | .key | .value | .blockEnd => true
      | _ => false
    if ks.any isDoc then "document"
    else if ks.any isFlow then "flow"
    else if ks.any isBlock then "block"
    else "leaf"

def slices : List String := ["leaf", "flow", "block", "document"]

/-- The token kinds `tokenEvents` reads (`TokenEvents.go`): everything else is trace-inert. -/
def traceKind : YamlToken → Bool
  | .anchor _ | .alias _ | .tag _ _ | .tagDirective _ _ | .documentStart | .documentEnd => true
  | _ => false

def hasEvents (s : String) : Bool :=
  match (both s).1 with
  | some (_ :: _) => true
  | _ => false

structure Tally where
  rows : Nat := 0
  scanned : Nat := 0
  lexed : Nat := 0
  bothOk : Nat := 0
  agree : Nat := 0
  disagree : List (String × List Event × List Event) := []
  scanOnly : List String := []
  lexOnly : Nat := 0
  eventRows : Nat := 0
  inert : Nat := 0          -- scanned rows whose trace is unchanged after dropping every non-trace kind
  tgOk : Nat := 0           -- scanned rows `checkTokenGrammar` accepts
  parseOk : Nat := 0        -- scanned rows `parseStream` accepts
  tgNotParse : List String := []
  parseNotTg : List String := []

def tally (rows : List String) : Tally := Id.run do
  let mut t : Tally := {}
  for s in rows do
    t := { t with rows := t.rows + 1 }
    let (a, b) := both s
    if a.isSome then t := { t with scanned := t.scanned + 1 }
    if b.isSome then t := { t with lexed := t.lexed + 1 }
    match a, b with
    | some ea, some eb =>
      t := { t with bothOk := t.bothOk + 1 }
      if ea == eb then t := { t with agree := t.agree + 1 }
      else t := { t with disagree := (s, ea, eb) :: t.disagree }
    | some _, none => t := { t with scanOnly := s :: t.scanOnly }
    | none, some _ => t := { t with lexOnly := t.lexOnly + 1 }
    | none, none => pure ()
    match scanFiltered s with
    | .ok ts =>
      if hasEvents s then t := { t with eventRows := t.eventRows + 1 }
      if tokenEvents (ts.filter fun p => traceKind p.val) == tokenEvents ts then
        t := { t with inert := t.inert + 1 }
      let tg := checkTokenGrammar ts
      let pk := (parseStream ts).toOption.isSome
      if tg then t := { t with tgOk := t.tgOk + 1 }
      if pk then t := { t with parseOk := t.parseOk + 1 }
      if tg && !pk then t := { t with tgNotParse := s :: t.tgNotParse }
      if pk && !tg then t := { t with parseNotTg := s :: t.parseNotTg }
    | .error _ => pure ()
  return t

/-- The two divergence shapes `RefLexCensus` pins: the private lexer folds a line-start `&x` into a
plain scalar the scanner ends, and reads an explicit `|2` indentation indicator the scanner honours. -/
def knownDivergence (s : String) : Bool :=
  s == "a: foo\n  &x\nb: *x" || s == "a: |2\n   *x\n  *y\n"

/-- First run (P2 REFUTED): `refLex` has no BOM arm — `\uFEFF--- a` is one `opaque` segment to it, while
the scanner drops the BOM and emits `documentStart` and `[202] l-document-prefix` has a `bom` constructor,
so the bridge's two sides agree and the lexer is the odd one out (census debt, not proof debt). -/
def bomRow (s : String) : Bool := s.toList.head? == some '\uFEFF'

/-- First run (P2 REFUTED): `&x a⏎&y b` — the scanner folds the second line into the plain scalar
`a &y b` (one anchor); the lexer reads `&y` at line start as a second anchor.  The grammar admits both
(`TraceOfBlockAmbiguity` pair 1), the scanner's reading is the parser's, and the bridge — an existence
statement — holds with the scanner's trace.  This is the block slice's plain-continuation boundary. -/
def plainContinuation (s : String) : Bool := s == "&x a\n&y b"

/-- The disagreeing rows of the first run, pinned as a SET so a fifth disagreement (or a vanished one)
fails here rather than drifting under the per-kind classification (review of the first cut). -/
def disagreeRows : List String :=
  ["\uFEFF--- a", "&x a\n&y b", "\uFEFF!t a", "\uFEFF...\n: a"]

/-- `parseStream`'s refusal is the state half (`undeclaredTagHandle`), never a shape `TokenGrammar` misses. -/
def stateRefusal (s : String) : Bool :=
  match scanFiltered s with
  | .ok ts => match parseStream ts with
    | .error (.undeclaredTagHandle ..) => true
    | _ => false
  | .error _ => false

/-! ### Smallest term-level instances of the bridge: `---` and `...` -/

private lemma eofComments (col : Nat) : SSLComments ⟨[], col⟩ ⟨[], col⟩ :=
  .withComment _ _ _ (.noSep _ _ (.eof col)) (.nil _)

/-- `---` alone: one explicit document with an empty node — trace `[beginDocument]`. -/
lemma traceOf_docStart : TLYamlStream ⟨['-', '-', '-'], 0⟩ ⟨[], 3⟩ [.beginDocument] :=
  .single _ _ _ _ [.beginDocument] [] (.nil _)
    (.some _ _ _ (.explicit _ _ _ (.withContent _ ⟨[], 3⟩ _ [] (.mk [])
      (.right _ _ _ (.mk _ ⟨[], 3⟩ _ [] [] ⟨.mk _, rfl⟩ ⟨eofComments 3, rfl⟩)))))
    (.nil _)

/-- `...` alone: no document, one suffix — trace `[endDocument]`. -/
lemma traceOf_docEnd : TLYamlStream ⟨['.', '.', '.'], 0⟩ ⟨[], 3⟩ [.endDocument] :=
  .single _ _ _ _ [] [.endDocument] (.nil _) (.none _)
    (.cons _ ⟨[], 3⟩ _ [.endDocument] [] (.mk _ ⟨[], 3⟩ _ (.mk []) (eofComments 3)) (.nil _))

end P99

def testTraceBridge (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 99: S3 proper — scanFiltered input = .ok ts → TraceOf input (tokenEvents ts), READ"
  let rows := P99.allRows
  let t := P99.tally rows
  let evStr (l : List L4YAML.Proofs.Serialization.SerializationWellFormed.Event) : String := String.intercalate "," (l.map fun e => s!"{repr e}")
  -- (i) the executable mirror: the scanner's trace against the reference lexer's, every probe row
  checkM state s!"P99(i) {t.rows} rows, {t.scanned} scanned, {t.lexed} lexed, {t.bothOk} both: scanner and skeleton traces agree on {t.agree}"
    (t.agree + t.disagree.length == t.bothOk) ""
  for (s, ea, eb) in t.disagree do
    checkM state s!"P99(i) disagreement is a BOM row (lexer debt), the plain-continuation shape, or a pinned RefLexCensus shape: {repr s}"
      (P99.bomRow s || P99.plainContinuation s || P99.knownDivergence s)
      s!"scanner={evStr ea} skeleton={evStr eb}"
  let dis := t.disagree.map (·.1)
  checkM state s!"P99(i) disagreements: {(dis.filter P99.bomRow).length} BOM rows (lexer debt), {(dis.filter P99.plainContinuation).length} plain-continuation, {(dis.filter P99.knownDivergence).length} RefLexCensus — exactly the pinned set of {P99.disagreeRows.length}"
    (dis.length == P99.disagreeRows.length && P99.disagreeRows.all (dis.contains ·) && t.agree + dis.length == t.bothOk)
    s!"got {repr dis}"
  checkM state s!"P99(i) no row the scanner accepts is refused by the lexer ({t.scanOnly.length} scanner-only; {t.lexOnly} lexer-only)"
    t.scanOnly.isEmpty s!"{repr t.scanOnly}"
  -- (ii) per slice (scanned rows, labelled by their tokens)
  let mut sliced := 0
  for sl in P99.slices do
    let rs := rows.filter (P99.sliceOf · == sl)
    let ts := P99.tally rs
    sliced := sliced + ts.rows
    checkM state s!"P99(ii) slice {sl}: {ts.rows} scanned rows, {ts.eventRows} event-bearing, {ts.agree} agree, {ts.disagree.length} disagree"
      (ts.scanned == ts.rows && ts.agree + ts.disagree.length == ts.bothOk) ""
  checkM state s!"P99(ii) the four slices partition the {t.scanned} scanned rows" (sliced == t.scanned) s!"{sliced}"
  -- (iii) consumer census, executable half: the trace reads six token kinds; every other kind
  -- (`.key`/`.value`/`.blockEnd`/flow ends/`.flowEntry`, `.comment`, `.streamStart`/`.streamEnd`, …) is inert
  checkM state s!"P99(iii) trace inert under every non-trace token kind on {t.inert} of {t.scanned} scanned rows"
    (t.inert == t.scanned) ""
  -- (iv) the (β) route's reach: `checkTokenGrammar` against `parseStream` on scanner output
  -- P5 REFUTED in kind: `TokenGrammar` is the shape half, so it accepts the rows `parseStream` refuses for
  -- STATE (`undeclaredTagHandle`); no scanner output is parser-accepted and grammar-refused
  checkM state s!"P99(iv) TokenGrammar accepts {t.tgOk} of {t.scanned} scanned rows; parseStream accepts {t.parseOk}; TG∧¬parse {t.tgNotParse.length} (all undeclaredTagHandle), parse∧¬TG {t.parseNotTg.length}"
    (t.tgNotParse.all P99.stateRefusal && t.parseNotTg.isEmpty) s!"TG-only={repr t.tgNotParse} parse-only={repr t.parseNotTg}"
  -- (v) the smallest instances, trace side (lemmas above) against the scanner side
  checkM state "P99(v) `---`: scanner trace = [beginDocument] (= traceOf_docStart)"
    ((P99.both "---").1 == some [.beginDocument]) s!"{repr (P99.both "---").1}"
  checkM state "P99(v) `...`: scanner trace = [endDocument] (= traceOf_docEnd)"
    ((P99.both "...").1 == some [.endDocument]) s!"{repr (P99.both "...").1}"
  checkM state "P99(v) empty: scanner trace = [] (= traceOf_empty)"
    ((P99.both "").1 == some []) ""
  -- (vi) the order the document slice must reproduce: beginDocument before the declareTags of its directives
  checkM state "P99(vi) `%TAG !e! tag:x⏎--- !e!a`: [beginDocument, declareTag !e!, useTag !e!]"
    ((P99.both "%TAG !e! tag:x\n--- !e!a").1 == some [.beginDocument, .declareTag "!e!", .useTag "!e!"])
    s!"{repr (P99.both "%TAG !e! tag:x\n--- !e!a").1}"
  checkM state "P99(vi) `%TAG !e! tag:x` without `---` is refused by the scanner (DirectivesClosed, S3 (b))"
    ((P99.both "%TAG !e! tag:x").1 == none) ""

/-! ## Priority 100: S3 slice (1), the leaf bridge — span ↔ payload, before proof
The leaf twins to be proved: for a scanned `.anchor name` / `.alias name` / `.tag handle suffix` token,
the annotated leaf relation (`TCNsAnchorProperty` / `TCNsAliasNode` / `TCNsTagProperty`, `TraceOf/Leaves.lean`)
holds on the lexeme's span with the trace `tokenEvent` assigns the token — i.e. `anchorEvents span =
[.defineAnchor name]`, `aliasEvents span = [.useAlias name]`, `tagEvents span = (tokenEvent (.tag handle _)).toList`.
Executable mirror: the span is the input from the token's byte offset to the next token's (the leaf event
functions read only the lexeme's own prefix, so the trailing text is inert); the legacy scanner leaves
`endPos` at `pos`, hence the next-token bound.  Also gridded: the boolean anchor-char class the lexer uses
(`isAnchorCharBool`) against `collectAnchorNameLoop`'s own condition, over every scalar value. -/
namespace P100
open L4YAML.Proofs.Serialization.TokenEvents (tokenEvent)
open L4YAML.Proofs.Serialization.TraceOf (anchorEvents aliasEvents tagEvents span)
open L4YAML.Proofs.Serialization.SerializationWellFormed (Event)
open L4YAML.Proofs.Serialization.EventsOf (handleOf)
open L4YAML.CharPredicates
open L4YAML.Surface

/-- Leaf boundary rows: every handle kind, anchor-name boundaries, empty/singleton lexemes, both
property orders, flow/block neighbours, BOM and non-ASCII names. -/
def own : List String :=
  [ "!", "!!", "!!x", "!e!", "!e!x", "!-!x", "!a-b!x", "!a%b!c", "!%!x", "!a!b!c", "!<tag:x>", "!<>", "!<tag:x>y",
    "!<tag:x> a", "!!str a", "!t a", "!t", "!a!", "!A1-!x",
    "&", "*", "& a", "&a", "*a", "&a,b", "[&a,b]", "[&a]", "{&a: b}", "&a#c", "&a: b", "*a: b", "&a\tb", "&a b",
    "&aé b", "&a\u0007", "&a\uFEFFb", "\uFEFF&a b", "&a *a", "&a\n*a", "- &a\n- *a", "&a\n!t b", "!t &a b", "&a !t b",
    "!t\n&a b", "&a\n!t\nb", "[!t &a b, *a]", "{!t &a b: *a}", "&a: !t b", "? &a\n: *a", "&a]", "&a}", "*a]", "&a\n",
    "&x [*x]", "&x {a: *x}", "&x\n- *x", "!<tag:x,y!h!> a", "!<!> a", "!<tag:x>!y", "!!x!y", "!e!x!y", "!e! x", "!e!\nx" ]

def allRows : List String := (P99.allRows ++ own).eraseDups

/-- Drop `n` UTF-8 bytes from a char list. -/
def dropBytes : List Char → Nat → List Char
  | l, 0 => l
  | [], _ => []
  | c :: cs, n => dropBytes cs (n - c.utf8Size)

/-- Take `bytes` UTF-8 bytes from a char list (a partial last char is dropped). -/
def takeBytes : List Char → Nat → List Char
  | _, 0 => []
  | [], _ => []
  | c :: cs, n => if n < c.utf8Size then [] else c :: takeBytes cs (n - c.utf8Size)

def spanAt (input : String) (a b : Nat) : List Char :=
  takeBytes (dropBytes input.toList a) (b - a)

def isLeaf : YamlToken → Bool
  | .anchor _ | .alias _ | .tag _ _ => true
  | _ => false

def leafEvents : YamlToken → List Char → List Event
  | .anchor _, sp => anchorEvents sp
  | .alias _, sp => aliasEvents sp
  | .tag _ _, sp => tagEvents sp
  | _, _ => []

def handleKind : YamlToken → String
  | .tag "" _ => "verbatim"
  | .tag "!" _ => "primary"
  | .tag "!!" _ => "secondary"
  | .tag _ _ => "named"
  | .anchor _ => "anchor"
  | .alias _ => "alias"
  | _ => "other"

structure Tally where
  rows : Nat := 0
  scanned : Nat := 0
  leaves : Nat := 0
  ok : Nat := 0
  byKind : List (String × Nat) := []
  bad : List (String × String × String) := []   -- row, token, (span events vs tokenEvent)

def bump (acc : List (String × Nat)) (k : String) : List (String × Nat) :=
  match acc.find? (·.1 == k) with
  | some _ => acc.map fun (a, n) => if a == k then (a, n + 1) else (a, n)
  | none => (k, 1) :: acc

def tally (rows : List String) : Tally := Id.run do
  let mut t : Tally := {}
  for s in rows do
    t := { t with rows := t.rows + 1 }
    match scanFiltered s with
    | .error _ => pure ()
    | .ok ts =>
      t := { t with scanned := t.scanned + 1 }
      let n := ts.size
      for i in [0:n] do
        let tk := ts[i]!
        if isLeaf tk.val then
          let b := if i + 1 < n then ts[i+1]!.pos.offset else s.utf8ByteSize
          let sp := spanAt s tk.pos.offset b
          let got := leafEvents tk.val sp
          let want := (tokenEvent tk.val).toList
          t := { t with leaves := t.leaves + 1, byKind := bump t.byKind (handleKind tk.val) }
          if got == want then t := { t with ok := t.ok + 1 }
          else t := { t with bad := (s, s!"{repr tk.val}", s!"span={repr (String.ofList sp)} got={repr got} want={repr want}") :: t.bad }
  return t

/-- `collectAnchorNameLoop`'s own acceptance condition, as written in `Scanner/NodeProperties.lean`. -/
def loopCond (c : Char) : Bool :=
  !isFlowIndicatorBool c && !isWhiteSpaceBool c && !isLineBreakBool c && isPrintableBool c && c != '\uFEFF'

def charMismatches : Nat := Id.run do
  let mut n := 0
  for k in [0:0x110000] do
    if k < 0xD800 || 0xDFFF < k then
      let c := Char.ofNat k
      if L4YAML.Proofs.Serialization.SourceEvents.isAnchorCharBool c != loopCond c then n := n + 1
  return n

def kindCount (t : Tally) (k : String) : Nat := (t.byKind.find? (·.1 == k)).map (·.2) |>.getD 0


/-! ### (vi)–(viii) The headline conclusions on positioned scanner states, directly

`scanAnchorOrAlias` / `scanTag` / `scanNextToken_dispatchContent` run from a state positioned
at the leaf's marker (the input advanced byte by byte to the real token's offset): the pushed
token array, the landing state (`input`/`inputEnd` kept, `col` moved by the lexeme's length,
`tokens` of the loops untouched) and the trace of the lexeme the scanner itself consumed —
the executable face of `ScannerSurfCorr s' sp'` and `TCNs*` in the twins.  The loop helpers at
fuel 0 / 1 / 2 / full with empty and non-empty accumulators. -/

/-- Advance a fresh state to byte offset `k` (bounded by the input's size). -/
def stateAt (input : String) (k : Nat) : ScannerState := Id.run do
  let mut st := ScannerState.mk' input
  for _ in [0:input.utf8ByteSize] do
    if st.offset < k then st := st.advance
  return st

/-- The leaf tokens of every scanned row, with the row and the next token's offset. -/
def leafSites (rows : List String) : List (String × Positioned YamlToken) := Id.run do
  let mut out := []
  for s in rows do
    match scanFiltered s with
    | .error _ => pure ()
    | .ok ts =>
      for tk in ts do
        if isLeaf tk.val then out := (s, tk) :: out
  return out.reverse

def isTrailing : ScanError → Bool
  | .trailingContent _ _ => true
  | _ => false

def siteWhy (s : String) (o : Nat) (e : ScanError) : String := s!"{repr s}@{o}: {repr e}"

structure Direct where
  runs : Nat := 0
  ok : Nat := 0
  refused : Nat := 0
  /-- The refused sites as `(row, offset)`, every one a `trailingContent` refusal (else `badRefusal`). -/
  refusedAt : List (String × Nat) := []
  badRefusal : List String := []
  okByKind : List (String × Nat) := []
  refusedByKind : List (String × Nat) := []
  bad : List String := []

def recordRefusal (d : Direct) (s : String) (o : Nat) (kind : String) (e : ScanError) : Direct :=
  let d := { d with refused := d.refused + 1 }
  let d := { d with refusedAt := (s, o) :: d.refusedAt }
  let d := { d with refusedByKind := bump d.refusedByKind kind }
  if isTrailing e then d else { d with badRefusal := siteWhy s o e :: d.badRefusal }

/-- The executable face of a twin's conclusion for a run `st → s'` that emitted `tk`. -/
def landingOk (s : String) (st s' : ScannerState) (tok : YamlToken) : Bool :=
  let sp := spanAt s st.offset s'.offset
  s'.tokens == st.tokens.push { pos := st.currentPos, val := tok } &&
  s'.input == st.input && s'.inputEnd == st.inputEnd && st.offset ≤ s'.offset &&
  s'.col == st.col + sp.length &&
  leafEvents tok sp == (tokenEvent tok).toList

def directRuns (rows : List String) : Direct × Direct × Direct := Id.run do
  let mut leaf : Direct := {}
  let mut tag : Direct := {}
  let mut disp : Direct := {}
  for (s, tk) in leafSites rows do
    let st := stateAt s tk.pos.offset
    -- the scanner's own leaf functions, no guards
    match tk.val with
    | .anchor _ | .alias _ =>
      leaf := { leaf with runs := leaf.runs + 1 }
      match scanAnchorOrAlias st (match tk.val with | .anchor _ => true | _ => false) with
      | .error e => leaf := { leaf with refused := leaf.refused + 1, bad := s!"{repr s}@{st.offset}: refused {repr e}" :: leaf.bad }
      | .ok s' =>
        let want := match tk.val with
          | .anchor _ => YamlToken.anchor ((s'.tokens.back?.map (·.val)).getD .placeholder |> fun t => match t with | .anchor n => n | _ => "")
          | _ => YamlToken.alias ((s'.tokens.back?.map (·.val)).getD .placeholder |> fun t => match t with | .alias n => n | _ => "")
        if (s'.tokens.back?.map (·.val)) == some tk.val && landingOk s st s' want then leaf := { leaf with ok := leaf.ok + 1 }
        else leaf := { leaf with bad := s!"{repr s}@{st.offset}: {repr tk.val} → {repr (s'.tokens.back?.map (·.val))} col {st.col}→{s'.col} off {st.offset}→{s'.offset}" :: leaf.bad }
    | .tag _ _ =>
      tag := { tag with runs := tag.runs + 1 }
      match scanTag st with
      | .error e => tag := { tag with refused := tag.refused + 1, bad := s!"{repr s}@{st.offset}: refused {repr e}" :: tag.bad }
      | .ok s' =>
        if (s'.tokens.back?.map (·.val)) == some tk.val && landingOk s st s' tk.val then tag := { tag with ok := tag.ok + 1 }
        else tag := { tag with bad := s!"{repr s}@{st.offset}: {repr tk.val} → {repr (s'.tokens.back?.map (·.val))} col {st.col}→{s'.col} off {st.offset}→{s'.offset}" :: tag.bad }
    | _ => pure ()
    -- the content dispatcher's arm (guards live: an alias needs its anchor defined)
    let c := match tk.val with | .anchor _ => '&' | .alias _ => '*' | _ => '!'
    let stD := match tk.val with | .alias n => { st with definedAnchors := #[n] } | _ => st
    disp := { disp with runs := disp.runs + 1 }
    match scanNextToken_dispatchContent stD c with
    | .error e =>
      disp := recordRefusal disp s st.offset (handleKind tk.val) e
    | .ok s'' =>
      if (s''.tokens.back?.map (·.val)) == some tk.val && landingOk s stD s'' tk.val then
        disp := { disp with ok := disp.ok + 1, okByKind := bump disp.okByKind (handleKind tk.val) }
      else disp := { disp with bad := s!"{repr s}@{st.offset}: dispatch {repr tk.val} → {repr (s''.tokens.back?.map (·.val))} col {stD.col}→{s''.col}" :: disp.bad }
  return (leaf, tag, disp)

/-- The dispatcher's refusals on the fresh (block-context) states, read on 2026-11-08: every one an
alias inside a flow collection, refused by the `*` arm's `validateAliasClose` as `trailingContent`
(`flowLevel = 0` on the direct run's state, so `,` / `]` / `}` after the alias reads as trailing). -/
def dispRefusedSites : List (String × Nat) :=
  [("[&x a, *x]", 7), ("{&x a: *x}", 7), ("[&x a: *x]", 7), ("[&x [*x]]", 5), ("{a: [&x b, *x]}", 11),
   ("[&x a,\n *x]", 8), ("{ &x a : *x }", 9), ("[!t &a b, *a]", 10), ("{!t &a b: *a}", 10),
   ("&x [*x]", 4), ("&x {a: *x}", 7)]

def kindOf (l : List (String × Nat)) (k : String) : Nat := (l.find? (·.1 == k)).map (·.2) |>.getD 0

structure Loops where
  runs : Nat := 0
  ok : Nat := 0
  bad : List String := []

def loopsOk (st s1 : ScannerState) : Bool :=
  s1.input == st.input && s1.inputEnd == st.inputEnd && s1.tokens == st.tokens && st.offset ≤ s1.offset

/-- The four loops at fuel 0 / 1 / 2 / full, accumulators `""` and `"pre"`, from the position after the marker. -/
def loopRuns (rows : List String) : Loops := Id.run do
  let mut L : Loops := {}
  let fuels (st : ScannerState) : List Nat := [0, 1, 2, st.inputEnd - st.offset]
  for (s, tk) in leafSites rows do
    let st := (stateAt s tk.pos.offset).advance
    for acc in ["", "pre"] do
      for f in fuels st do
        -- anchor-name loop: the name is acc ++ the consumed span, all isAnchorCharBool
        let (name, s1) := collectAnchorNameLoop st acc f
        let sp := spanAt s st.offset s1.offset
        L := { L with runs := L.runs + 1 }
        if loopsOk st s1 && name.toList == acc.toList ++ sp && sp.all L4YAML.Proofs.Serialization.SourceEvents.isAnchorCharBool
            && s1.col == st.col + sp.length then L := { L with ok := L.ok + 1 }
        else L := { L with bad := s!"anchor-loop {repr s}@{st.offset} acc={repr acc} fuel={f}: name={repr name} span={repr (String.ofList sp)}" :: L.bad }
        -- tag-handle loop: span = word chars (++ '!' with the bang); no bang at full fuel ⇒ stop char not word, not '!'
        let (w, bang, s2) := collectTagHandleLoop st acc f
        let sp2 := spanAt s st.offset s2.offset
        let body := w.toList.drop acc.length
        let stop := (dropBytes s.toList s2.offset).head?
        let stopOk := bang || f < st.inputEnd - st.offset || (match stop with | none => true | some c => !isWordCharBool c && c != '!')
        L := { L with runs := L.runs + 1 }
        if loopsOk st s2 && w.toList.take acc.length == acc.toList && sp2 == body ++ (if bang then ['!'] else []) && body.all isWordCharBool && stopOk
            && s2.col == st.col + sp2.length then L := { L with ok := L.ok + 1 }
        else L := { L with bad := s!"handle-loop {repr s}@{st.offset} acc={repr acc} fuel={f}: w={repr w} bang={bang} span={repr (String.ofList sp2)}" :: L.bad }
        -- tag-suffix loop: suffix = acc ++ the consumed span
        let (suf, s3) := collectTagSuffixLoop st acc f
        let sp3 := spanAt s st.offset s3.offset
        L := { L with runs := L.runs + 1 }
        if loopsOk st s3 && suf.toList == acc.toList ++ sp3 && s3.col == st.col + sp3.length then L := { L with ok := L.ok + 1 }
        else L := { L with bad := s!"suffix-loop {repr s}@{st.offset} acc={repr acc} fuel={f}: suf={repr suf} span={repr (String.ofList sp3)}" :: L.bad }
        -- verbatim loop: span = uri chars (++ '>' with the close)
        let (uri, close, s4) := collectVerbatimTagLoop st acc f
        let sp4 := spanAt s st.offset s4.offset
        L := { L with runs := L.runs + 1 }
        if loopsOk st s4 && sp4 == uri.toList.drop acc.length ++ (if close then ['>'] else []) && s4.col == st.col + sp4.length then L := { L with ok := L.ok + 1 }
        else L := { L with bad := s!"verbatim-loop {repr s}@{st.offset} acc={repr acc} fuel={f}: uri={repr uri} close={close} span={repr (String.ofList sp4)}" :: L.bad }
  return L

/-! ### Smallest term-level instances: `&x`, `*x`, `!` with the token's trace -/

private lemma ns_x : isNsAnchorChar 'x' := by unfold isNsAnchorChar isNsChar; decide

private lemma gnot_empty {P : Char → Prop} (col : Nat) : GNot (GChar P) ⟨[], col⟩ :=
  fun _ h => by cases h

lemma traceOf_anchor_x : L4YAML.Proofs.Serialization.TraceOf.TCNsAnchorProperty
    ⟨['&', 'x'], 0⟩ ⟨[], 2⟩ [.defineAnchor "x"] :=
  ⟨.mk ['x'] 0 ⟨[], 2⟩ (.mk _ _ _ (.mk 'x' [] 1 ns_x) (.nil _)) (gnot_empty 2), rfl⟩

lemma traceOf_alias_x : L4YAML.Proofs.Serialization.TraceOf.TCNsAliasNode
    ⟨['*', 'x'], 0⟩ ⟨[], 2⟩ [.useAlias "x"] :=
  ⟨.mk ['x'] 0 ⟨[], 2⟩ (.mk _ _ _ (.mk 'x' [] 1 ns_x) (.nil _)) (gnot_empty 2), rfl⟩

lemma traceOf_tag_bang : L4YAML.Proofs.Serialization.TraceOf.TCNsTagProperty
    ⟨['!'], 0⟩ ⟨[], 1⟩ [.useTag "!"] :=
  ⟨.nonSpecific [] 0 (gnot_empty 1), rfl⟩

end P100


/-! ## Priority 101 — S3 slice (2): document markers and the `tokenEvents` algebra, before proof

Item 459's NEXT.  The statements: (A) `go (l₁ ++ l₂) p = (goOut l₁ p).1 ++ go l₂ (goOut l₁ p).2`
with `goOut` the state-passing twin of `TokenEvents.go` (events emitted, pending handles left),
`.documentStart` flushing the pending `%TAG` handles as `declareTag`s after `beginDocument`;
(B) the scanner's `scanDocumentStart` / `scanDocumentEnd` / `scanDirective` arms land on
`SCDirectivesEnd` / `SCDocumentEnd` / `ScannedDirective` with the token they push and the
`TLDirective` payload `declaredHandle (span) = named handle`. -/
namespace P101
open L4YAML.Proofs.Serialization.TokenEvents (go goOut tokenEvents tokenEvent isNamedHandle tok)
open L4YAML.Proofs.Serialization.SerializationWellFormed (Event)

def own : List String :=
  ["---\na", "--- a", "---", "---\n", "...", "...\n", "a\n...", "a\n...\nb", "---\na\n...",
   "---\na\n...\n---\nb", "---\n...\n", "--- ...", "---\n...", "---a", "...a", "... a",
   "%YAML 1.2\n---\na", "%TAG !e! tag:x,2000:\n---\n!e!a b", "%TAG ! tag:x,2000:\n---\n!a b",
   "%TAG !! tag:x,2000:\n---\n!!str b", "%TAG !e! tag:x:\n%YAML 1.2\n---\na",
   "%YAML 1.2\n%TAG !e! tag:x:\n---\na", "%TAG !a! tag:a:\n%TAG !b! tag:b:\n%TAG !c! tag:c:\n---\n!a!x !b!y",
   "%FOO bar\n---\na", "%TAG !e! tag:x:\n%FOO\n---\na", "%TAG !e! tag:x:\n---\na\n...\n%TAG !f! tag:y:\n---\nb",
   "%TAG !e! tag:x:\n---\na\n---\nb", "%TAG !e! tag:x:\n---\n...\n---\nb", "%TAG !e! tag:x: # c\n---\na",
   "%TAG !e-1! tag:x:\n---\na", "%TAG !e! tag:x:\n---\n%TAG !f! tag:y:\n---\nb",
   "\uFEFF---\na", "\uFEFFa\n...", "\uFEFF%TAG !e! tag:x:\n---\na", "\uFEFF%YAML 1.2\n---\na",
   "---\n- a\n- b\n...", "---\na: b\n---\nc: d", "--- |\n  x\n...", "--- !!str a", "--- &x a\n--- *x",
   "a\n---\nb", "a\n---\n...\n---\nb", "- a\n---\n- b", "a: b\n...\n---\nc: d",
   "%TAG !bad tag:x:\n---\na", "%TAG !e! tag:x: junk\n---\na", "a\n%TAG !e! tag:x:\n---\nb",
   "%TAG !e! tag:x:\n...", "%TAG !e! tag:x:\na", "%", "%TAG", "%TAG !e!", "%TAG !e! tag:x:",
   "%YAML 1.2\n%YAML 1.2\n---\na", "---\n%TAG !e! tag:x:\n---\na",
   -- separation after `%TAG`: none / tab / two spaces / none before the prefix
   "%TAG!e! tag:x:\n---\n!e!a b", "%TAGX !e! tag:x:\n---\na", "%TAG\t!e! tag:x:\n---\na",
   "%TAG  !e!  tag:x:\n---\na", "%TAG !e!tag:x:\n---\na", "%YAML 1.2 !e!\n---\na",
   -- handle shapes the lexer's `! word+ !` prefix read and the scanner's whole-run read could split on
   "%TAG !e!x! tag:x:\n---\na", "%TAG !e!! tag:x:\n---\na", "%TAG !!e! tag:x:\n---\na",
   "%TAG !e tag:x:\n---\na", "%TAG !-e! tag:x:\n---\n!-e!a b", "%TAG !e-1! tag:x:\n---\na",
   "%TAG !e!\n---\na", "%TAG\n---\na", "%TAG !e! tag:x: #c\n---\na", "%TAG !e! tag:x:\r\n---\na"]

def lineAt (s : String) (o : Nat) : List Char :=
  (P100.dropBytes s.toList o).takeWhile (fun c => c != '\n' && c != '\r')

def allRows : List String := (P100.allRows ++ own).eraseDups

/-- Pending-handle states every split starts from: none, one, two (most recent first). -/
def startPendings : List (List String) := [[], ["!a!"], ["!b!", "!a!"]]

def namedHandles (l : List (Positioned YamlToken)) : List String :=
  l.filterMap fun t => match t.val with
    | .tagDirective h _ => if isNamedHandle h then some h else none
    | _ => none

/-- The lexer's named handles of a row: `declaredHandle` on every column-0 `%` line. -/
def lexerHandles (s : String) : List String :=
  (s.splitOn "\n").filterMap fun ln =>
    match ln.toList with
    | '%' :: _ => L4YAML.Proofs.Serialization.EventsOf.declaredHandle (ln.toList.takeWhile (· != '\r'))
    | _ => none

/-- Scanned rows where the lexer's `declaredHandle` and the scanner's named `%TAG` tokens disagree. -/
def lexerDisagree (rows : List String) : List String := Id.run do
  let mut out := []
  for s in rows do
    match scanFiltered s with
    | .error _ => pure ()
    | .ok ts => if lexerHandles s != namedHandles ts.toList then out := s :: out
  return out.reverse

structure Tally where
  rows : Nat := 0
  scanned : Nat := 0
  refused : Nat := 0
  splits : Nat := 0
  splitBad : List String := []
  starts : Nat := 0
  startBad : List String := []
  ends : Nat := 0
  beginEv : Nat := 0
  endEv : Nat := 0
  dirs : Nat := 0
  namedDirs : Nat := 0
  dirBad : List String := []
  pendingAtEnd : Nat := 0

def tally (rows : List String) : Tally := Id.run do
  let mut t : Tally := {}
  for s in rows do
    t := { t with rows := t.rows + 1 }
    match scanFiltered s with
    | .error _ => t := { t with refused := t.refused + 1 }
    | .ok ts =>
      t := { t with scanned := t.scanned + 1 }
      let l := ts.toList
      let evs := tokenEvents ts
      -- (A) the append law at every split from empty AND nonempty pending handles (the production
      -- `TokenEvents.goOut`, not a copy), and the whole-stream reading
      for p in startPendings do
        let full := go l p
        for k in [0:l.length + 1] do
          let r := goOut (l.take k) p
          t := { t with splits := t.splits + 1 }
          if full != r.1 ++ go (l.drop k) r.2 then
            t := { t with splitBad := s!"{repr s} p={repr p} k={k}" :: t.splitBad }
        let whole := goOut l p
        if full != whole.1 ++ whole.2.reverse.map .declareTag then
          t := { t with splitBad := s!"{repr s} p={repr p} whole" :: t.splitBad }
      if evs != go l [] then t := { t with splitBad := s!"{repr s} tokenEvents" :: t.splitBad }
      let whole := goOut l []
      if !whole.2.isEmpty then t := { t with pendingAtEnd := t.pendingAtEnd + 1 }
      -- (B) every documentStart flushes the named handles since the previous one, in order
      let mut i := 0
      let mut prev := 0
      for tk in l do
        match tk.val with
        | .documentStart =>
          t := { t with starts := t.starts + 1 }
          let r := goOut (l.take i) []
          let named := namedHandles ((l.take i).drop prev)
          let tail := go (l.drop i) r.2
          if r.2.reverse != named || !(tail.take (named.length + 1) == .beginDocument :: named.map .declareTag) then
            t := { t with startBad := s!"{repr s} i={i}" :: t.startBad }
          prev := i + 1
        | .documentEnd => t := { t with ends := t.ends + 1 }
        | .tagDirective h _ =>
          t := { t with dirs := t.dirs + 1 }
          if isNamedHandle h then t := { t with namedDirs := t.namedDirs + 1 }
          -- the TLDirective payload: the lexer's declaredHandle on the directive line = the named handle
          let dh := L4YAML.Proofs.Serialization.EventsOf.declaredHandle (lineAt s tk.pos.offset)
          if dh != (if isNamedHandle h then some h else none) then
            t := { t with dirBad := s!"{repr s}@{tk.pos.offset}: {repr dh} vs {repr h}" :: t.dirBad }
        | _ => pure ()
        i := i + 1
      t := { t with beginEv := t.beginEv + (evs.filter (· == .beginDocument)).length,
                    endEv := t.endEv + (evs.filter (· == .endDocument)).length }
  return t

structure Direct where
  runs : Nat := 0
  ok : Nat := 0
  refused : Nat := 0
  refusedWhy : List String := []
  bad : List String := []

/-- The arms run directly on a fresh state positioned at the marker / directive. -/
def directRuns (rows : List String) : Direct × Direct × Direct := Id.run do
  let mut ds : Direct := {}
  let mut de : Direct := {}
  let mut dd : Direct := {}
  for s in rows do
    match scanFiltered s with
    | .error _ => pure ()
    | .ok ts =>
      for tk in ts do
        let st := P100.stateAt s tk.pos.offset
        match tk.val with
        | .documentStart =>
          ds := { ds with runs := ds.runs + 1 }
          let s' := scanDocumentStart st
          let sp := P100.spanAt s st.offset s'.offset
          if s'.tokens == st.tokens.push { pos := st.currentPos, val := .documentStart } &&
             sp == ['-', '-', '-'] && s'.col == st.col + 3 && s'.input == st.input &&
             s'.inputEnd == st.inputEnd && s'.definedAnchors.isEmpty && !s'.allowDirectives
          then ds := { ds with ok := ds.ok + 1 }
          else ds := { ds with bad := s!"{repr s}@{st.offset}" :: ds.bad }
        | .documentEnd =>
          de := { de with runs := de.runs + 1 }
          match scanDocumentEnd st with
          | .error e => de := { de with refused := de.refused + 1, refusedWhy := s!"{repr s}@{st.offset}: {repr e}" :: de.refusedWhy }
          | .ok s' =>
            let sp := P100.spanAt s st.offset s'.offset
            if s'.tokens == st.tokens.push { pos := st.currentPos, val := .documentEnd } &&
               sp == ['.', '.', '.'] && s'.col == st.col + 3 && s'.input == st.input && s'.allowDirectives
            then de := { de with ok := de.ok + 1 }
            else de := { de with bad := s!"{repr s}@{st.offset}" :: de.bad }
          -- the guard: directives pending refuse `...`
          match scanDocumentEnd { st with directivesPresent := true } with
          | .error (.directiveWithoutDocument _) => pure ()
          | _ => de := { de with bad := s!"{repr s}@{st.offset}: directivesPresent not refused" :: de.bad }
        | .tagDirective h pfx =>
          dd := { dd with runs := dd.runs + 1 }
          match scanDirective st with
          | .error e => dd := { dd with refused := dd.refused + 1, refusedWhy := s!"{repr s}@{st.offset}: {repr e}" :: dd.refusedWhy }
          | .ok s' =>
            let sp := P100.spanAt s st.offset s'.offset
            let dh := L4YAML.Proofs.Serialization.EventsOf.declaredHandle (lineAt s st.offset)
            if s'.tokens == st.tokens.push { pos := st.currentPos, val := .tagDirective h pfx } &&
               sp.head? == some '%' && s'.input == st.input && s'.directivesPresent &&
               dh == (if isNamedHandle h then some h else none)
            then dd := { dd with ok := dd.ok + 1 }
            else dd := { dd with bad := s!"{repr s}@{st.offset}: span {repr (String.ofList sp)} dh {repr dh}" :: dd.bad }
          match scanDirective { st with allowDirectives := false } with
          | .error (.directiveAfterContent _) => pure ()
          | _ => dd := { dd with bad := s!"{repr s}@{st.offset}: directiveAfterContent not refused" :: dd.bad }
        | _ => pure ()
  return (ds, de, dd)

end P101

section P101Test
open L4YAML.Proofs.Serialization.TokenEvents (go tokenEvents tokenEvent isNamedHandle tok)
open L4YAML.Proofs.Serialization.SerializationWellFormed (Event)

def testDocBridge (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 101: S3 slice (2) — document markers and the tokenEvents algebra, before proof"
  let t := P101.tally P101.allRows
  checkM state s!"P101(i) {t.rows} rows, {t.scanned} scanned, {t.refused} refused" (t.scanned ≥ 400 && t.refused ≥ 8) ""
  checkM state s!"P101(ii) go (l₁ ++ l₂) p = (goOut l₁ p).1 ++ go l₂ (goOut l₁ p).2 at every split from pending [] / [!a!] / [!b!, !a!]: {t.splits} splits, {t.splitBad.length} bad; whole-stream flush of the pending handles holds; {t.pendingAtEnd} rows end with pending handles"
    (t.splitBad.isEmpty && t.splits ≥ 6000) s!"{repr (t.splitBad.take 6)}"
  checkM state s!"P101(iii) every documentStart ({t.starts}) flushes exactly the named handles since the previous one, in order, after beginDocument: {t.startBad.length} bad"
    (t.startBad.isEmpty && t.starts ≥ 60) s!"{repr (t.startBad.take 6)}"
  checkM state s!"P101(iv) documentStart tokens {t.starts} = beginDocument events {t.beginEv}; documentEnd tokens {t.ends} = endDocument events {t.endEv}"
    (t.starts == t.beginEv && t.ends == t.endEv && t.ends ≥ 15) ""
  checkM state s!"P101(v) TLDirective payload: declaredHandle (directive line) = the named handle on every %TAG ({t.dirs} directives, {t.namedDirs} named): {t.dirBad.length} bad"
    (t.dirBad.isEmpty && t.namedDirs ≥ 10 && t.dirs > t.namedDirs) s!"{repr (t.dirBad.take 6)}"
  let (ds, de, dd) := P101.directRuns P101.allRows
  checkM state s!"P101(vi) scanDocumentStart direct: {ds.runs} runs, {ds.ok} with the token / '---' span / col+3 / resets, {ds.bad.length} bad"
    (ds.bad.isEmpty && ds.ok == ds.runs && ds.runs ≥ 60) s!"{repr (ds.bad.take 6)}"
  checkM state s!"P101(vii) scanDocumentEnd direct: {de.runs} runs, {de.ok} with the token / '...' span / col+3, {de.refused} refused, {de.bad.length} bad; directivesPresent refused on every one"
    (de.bad.isEmpty && de.ok == de.runs && de.refused == 0 && de.runs ≥ 15) s!"{repr (de.bad.take 6)} {repr (de.refusedWhy.take 4)}"
  checkM state s!"P101(viii) scanDirective direct on %TAG: {dd.runs} runs, {dd.ok} with the token / '%'-span / declaredHandle, {dd.refused} refused, {dd.bad.length} bad; allowDirectives=false refused on every one"
    (dd.bad.isEmpty && dd.ok == dd.runs && dd.refused == 0 && dd.runs ≥ 15) s!"{repr (dd.bad.take 6)} {repr (dd.refusedWhy.take 4)}"
  -- (x) the TLDirective payload against the scanner on every directive LINE (not only on tagDirective tokens):
  -- predicted REFUTED by the scratch probe — `%TAG!e! …` is a reserved directive to the scanner and to
  -- `ScannedDirective` (no separation after `TAG`), while `declaredHandle` accepts zero separation.
  let dis := P101.lexerDisagree P101.allRows
  -- Before the ruling this read TWO rows: the BOM row (P99's known lexer debt — no BOM arm, so the `%`
  -- line is not at column 0) and `%TAG!e! …`, the slice-(2) refutation: `TLDirective`'s payload named a
  -- handle the scanner (and `ScannedDirective.tag`'s separation premise) does not declare, because
  -- `namedTagDeclarationAt` accepted zero separation after `%TAG`.  Ruling (α): the lexer now requires
  -- `[88]`'s `s-separate-in-line`; the BOM row alone remains.
  checkM state s!"P101(x) lexer declaredHandle vs scanner named %TAG per row: exactly the BOM row disagrees ({dis.length}): {repr dis}"
    (dis == ["\uFEFF%TAG !e! tag:x:\n---\na"]) ""
  checkM state "P101(x) %TAG!e! (no separation) declares nothing to the lexer, as to the scanner"
    (L4YAML.Proofs.Serialization.EventsOf.declaredHandle "%TAG!e! tag:x:".toList == none &&
     P101.namedHandles ((scanFiltered "%TAG!e! tag:x:\n---\n!e!a b").toOption.getD #[]).toList == []) ""
  -- (ix) term-level instances of the algebra
  checkM state "P101(ix) goOut [documentStart] [\"!e!\"] = ([beginDocument, declareTag !e!], [])"
    (L4YAML.Proofs.Serialization.TokenEvents.goOut [tok .documentStart] ["!e!"] == ([.beginDocument, .declareTag "!e!"], [])) ""
  checkM state "P101(ix) goOut [%TAG !e!, %TAG !, %YAML-shaped reserved] [] leaves pending [!e!]"
    ((L4YAML.Proofs.Serialization.TokenEvents.goOut [tok (.tagDirective "!e!" "x"), tok (.tagDirective "!" "y"), tok (.tagDirective "!!" "z")] []) == ([], ["!e!"])) ""
  checkM state "P101(ix) go [documentEnd] p = [endDocument] ++ flush p"
    (go [tok .documentEnd] ["!a!"] == [.endDocument, .declareTag "!a!"]) ""

end P101Test

/-! ## Priority 102 — S3 slice (3), first PR: flow indicators and quoted scalars as `TraceOf` leaves, before proof

Item 463's NEXT.  The statements: the `[` / `{` / `]` / `}` / `,` arms of
`scanNextToken_dispatchStructural` push exactly their indicator token over a one-character
span (`GLit`, trace `[]` — the token is silent under `goOut`), and `scanDoubleQuoted` /
`scanSingleQuoted` (the `"` / `'` arms of `scanNextToken_dispatchContent`) push one quoted
scalar token over the quoted lexeme (`SCDoubleQuoted` / `SCSingleQuoted` → `TFlowContent … []`).
Every token kind named here is trace-inert, so the whole first PR adds `[]` to a trace; the grid
checks the token / span / landing shape the lemmas will state and the guards the arms refuse on. -/
namespace P102
open L4YAML.Proofs.Serialization.TokenEvents (go goOut tokenEvent tok)
open L4YAML.Proofs.Serialization.SerializationWellFormed (Event)

def own : List String :=
  [-- nesting 0–3, empty / singleton, trailing commas, `,` after each kind
   "[]", "{}", "[a]", "{a: b}", "[a, b]", "{a: b, c: d}", "[a,]", "{a: b,}", "[,]", "[a,,b]",
   "[[]]", "[[[]]]", "[[[[]]]]", "{a: {b: {c: {}}}}", "[{}]", "{a: []}", "[[a], {b: c}]",
   "[a, [b, c], {d: e}, *x, &y z, !t w, \"q\", 'r', , ]", "[&a x, *a]", "[!!str a, !e!t b]",
   "{a, b: c, ? d : e, \"f\": 'g'}", "[a, b]: c", "? [a]\n: {b: c}", "- [a]\n- {b: c}",
   "{[a]: b}", "[{a: b}: c]", "[a\n, b\n]", "[\n  a,\n  b\n]", "{\n  a: b,\n  c: d\n}",
   "[a #c\n, b]", "[a, b] # tail", "---\n[a]\n...", "%TAG !e! tag:x:\n---\n[!e!a, b]",
   "[a, b, c, d]", "{a: 1, b: 2, c: 3}", "[[a, b], [c, d]]", "[a, b, c, d, e, f]",
   "{a: [b, c], d: {e: f, g: h}}", "[\"a\", \"b\", \"c\", 'd', 'e']", "[a, {b: c, d: e}, [f, g]]",
   "{? a : b, ? c : d}", "[*x, *y, *z]", "[&a 1, &b 2, &c 3]", "[a,b,c]", "{a: b,c: d}",
   -- closers / separators outside or against the wrong opener (refused)
   "]", "}", ",", "a]", "a}", "a,", "{a]", "[a}", "[a", "{a: b", "[a]]", "{a: b}}",
   -- quoted scalars: empty, escapes, folds, doubled quote, keys, flow / block context, BOM
   "\"\"", "''", "\"a\"", "'a'", "\"a b\"", "'a b'", "\"\\n\\t\\\\\\\"\"", "\"\\u0041\\x41\\U00000041\"",
   "'it''s'", "'''", "\"a\n  b\"", "'a\n b'", "\"a\\\n  b\"", "\"a\n\n  b\"", "\"a   \n   b\"",
   "k: \"v\"", "k: 'v'", "\"k\": v", "'k': v", "- \"a\"\n- 'b'", "[\"a\", 'b']", "{\"a\": 'b'}",
   "[\"a\", \"b\"]", "{'a': 'b', \"c\": \"d\"}", "\"a\": \"b\"", "? \"a\"\n: 'b'", "\"a\" # c",
   "\"a\"\n\"b\"", "--- \"a\"", "\"a\"\n---\n'b'", "\uFEFF\"a\"", "\uFEFF[a]", "&x \"a\"", "!!str 'a'",
   "\"\\q\"", "\"abc", "'abc", "\"a\nb", "k: \"a\n\nb\"", "\"a\\\"b\"", "'a\"b'", "\"a'b\"",
   -- quoted IMPLICIT KEYS spanning a line (review findings, slice (3) PR 1): the key twins'
   -- one-line premise is NOT always available — the scanner accepts these, and so do the encoded
   -- grammar (`TFlowMapEntry.implicitValue` / `TFlowSeqEntry.pairValue` read the key at `.flowIn`),
   -- `refLex` and `checkTokenGrammar`; the spec's `[154]` one-line rule for flow pairs is not encoded.
   "{\"a\n b\": c}", "[\"a\n b\": c]", "{'a\n b': c}", "\"a\n b\": c", "{\"a b\": c}", "{'a': b, \"c\n d\": e}"]

def allRows : List String := (P101.allRows ++ own).eraseDups

/-- The token kinds this slice's first PR speaks of. -/
def flowKind : YamlToken → Option String
  | .flowSequenceStart => some "["
  | .flowMappingStart => some "{"
  | .flowSequenceEnd => some "]"
  | .flowMappingEnd => some "}"
  | .flowEntry => some ","
  | .scalar _ .doubleQuoted => some "dq"
  | .scalar _ .singleQuoted => some "sq"
  | _ => none

/-- The flow stack the scanner holds before token `i` (`[` pushes `true`, `{` pushes `false`). -/
def flowCtxBefore (ts : Array (Positioned YamlToken)) (i : Nat) : Array Bool := Id.run do
  let mut st : Array Bool := #[]
  for tk in ts.toList.take i do
    match tk.val with
    | .flowSequenceStart => st := st.push true
    | .flowMappingStart => st := st.push false
    | .flowSequenceEnd | .flowMappingEnd => st := st.pop
    | _ => pure ()
  return st

/-- The fresh state at a token, carrying the scanner's flow context AND its prior tokens (so a lemma
that lost or rewrote the prefix would be refuted, and the adjacency guard sees the real predecessor). -/
def withFlow (st : ScannerState) (ctx : Array Bool) (prior : Array (Positioned YamlToken)) : ScannerState :=
  { st with flowLevel := ctx.size, flowStack := ctx, tokens := prior }

structure Tally where
  rows : Nat := 0
  scanned : Nat := 0
  refused : Nat := 0
  byKind : List (String × Nat) := []
  silentBad : List String := []
  openRuns : Nat := 0
  openBad : List String := []
  closeRuns : Nat := 0
  closeRefused : List String := []
  closeBad : List String := []
  guardBad : List String := []
  entryRuns : Nat := 0
  entryRefused : List String := []
  entryBad : List String := []
  quotedRuns : Nat := 0
  quotedRefused : List String := []
  quotedBad : List String := []
  dispBad : List String := []
  keySites : Nat := 0
  keyMultiLine : List (String × Nat) := []

/-- The lemmas' token conclusion, exactly: the prior tokens are kept and one token is pushed at
`currentPos` (`endPos` defaulting to it, as `emit` / `emitAt` write it). -/
def pushedOne (st s' : ScannerState) (v : YamlToken) : Bool :=
  s'.tokens == st.tokens.push { pos := st.currentPos, val := v }

def tally (rows : List String) : Tally := Id.run do
  let mut t : Tally := {}
  for s in rows do
    t := { t with rows := t.rows + 1 }
    match scanFiltered s with
    | .error _ => t := { t with refused := t.refused + 1 }
    | .ok ts =>
      t := { t with scanned := t.scanned + 1 }
      for i in [0:ts.size] do
        let tk := ts[i]!
        match flowKind tk.val with
        | none => pure ()
        | some k =>
          t := { t with byKind := P100.bump t.byKind k }
          -- (A) silent under the production fold, from every pending state
          if tokenEvent tk.val != none ||
             P101.startPendings.any (fun p => goOut [tk] p != ([], p)) then
            t := { t with silentBad := s!"{repr s}@{tk.pos.offset}" :: t.silentBad }
          -- (B) the arm run directly on a fresh state at the offset with the row's flow context
          let st := withFlow (P100.stateAt s tk.pos.offset) (flowCtxBefore ts i) (ts.extract 0 i)
          let site := s!"{repr s}@{tk.pos.offset}"
          match tk.val with
          | .flowSequenceStart | .flowMappingStart =>
            t := { t with openRuns := t.openRuns + 1 }
            let isSeq := tk.val == .flowSequenceStart
            let s' := if isSeq then scanFlowSequenceStart st else scanFlowMappingStart st
            let sp := P100.spanAt s st.offset s'.offset
            if pushedOne st s' tk.val && sp == [if isSeq then '[' else '{'] && s'.col == st.col + 1 &&
               s'.flowLevel == st.flowLevel + 1 && s'.flowStack.back? == some isSeq &&
               s'.input == st.input && s'.inputEnd == st.inputEnd
            then pure ()
            else t := { t with openBad := site :: t.openBad }
            match scanNextToken_dispatchFlowIndicators st (if isSeq then '[' else '{') with
            | .ok (some s'') => if s''.tokens != s'.tokens then t := { t with dispBad := site :: t.dispBad }
            | _ => t := { t with dispBad := s!"{site}: dispatcher" :: t.dispBad }
          | .flowSequenceEnd | .flowMappingEnd =>
            t := { t with closeRuns := t.closeRuns + 1 }
            let isSeq := tk.val == .flowSequenceEnd
            let c := if isSeq then ']' else '}'
            match scanNextToken_dispatchFlowIndicators st c with
            | .ok (some s') =>
              let sp := P100.spanAt s st.offset s'.offset
              if pushedOne st s' tk.val && sp == [c] && s'.col == st.col + 1 &&
                 s'.flowLevel + 1 == st.flowLevel && s'.flowStack.size + 1 == st.flowStack.size &&
                 s'.input == st.input
              then pure ()
              else t := { t with closeBad := site :: t.closeBad }
            | .ok none => t := { t with closeBad := s!"{site}: none" :: t.closeBad }
            | .error e => t := { t with closeRefused := s!"{site}: {repr e}" :: t.closeRefused }
            -- the two guards
            match scanNextToken_dispatchFlowIndicators (withFlow st #[] st.tokens) c with
            | .error (.flowEndOutsideFlow ..) => pure ()
            | _ => t := { t with guardBad := s!"{site}: level 0 not refused" :: t.guardBad }
            let flipped := st.flowStack.pop.push (!isSeq)
            match scanNextToken_dispatchFlowIndicators (withFlow st flipped st.tokens) c with
            | .error (.mismatchedFlowClose ..) => pure ()
            | _ => t := { t with guardBad := s!"{site}: mismatch not refused" :: t.guardBad }
          | .flowEntry =>
            t := { t with entryRuns := t.entryRuns + 1 }
            match scanNextToken_dispatchFlowIndicators st ',' with
            | .ok (some s') =>
              let sp := P100.spanAt s st.offset s'.offset
              if pushedOne st s' .flowEntry && sp == [','] && s'.col == st.col + 1 &&
                 s'.flowLevel == st.flowLevel && s'.input == st.input
              then pure ()
              else t := { t with entryBad := site :: t.entryBad }
            | .ok none => t := { t with entryBad := s!"{site}: none" :: t.entryBad }
            | .error e => t := { t with entryRefused := s!"{site}: {repr e}" :: t.entryRefused }
            match scanNextToken_dispatchFlowIndicators (withFlow st #[] st.tokens) ',' with
            | .error (.flowEndOutsideFlow ..) => pure ()
            | _ => t := { t with guardBad := s!"{site}: ',' at level 0 not refused" :: t.guardBad }
          | .scalar _ style =>
            t := { t with quotedRuns := t.quotedRuns + 1 }
            let dq := style == .doubleQuoted
            let q := if dq then '"' else '\''
            match (if dq then scanDoubleQuoted st else scanSingleQuoted st) with
            | .error e => t := { t with quotedRefused := s!"{site}: {repr e}" :: t.quotedRefused }
            | .ok s' =>
              let sp := P100.spanAt s st.offset s'.offset
              if pushedOne st s' tk.val && sp.head? == some q && sp.getLast? == some q &&
                 sp.length ≥ 2 && s'.peekBack? == some q && s'.input == st.input
              then pure ()
              else t := { t with quotedBad := s!"{site}: span {repr (String.ofList sp)}" :: t.quotedBad }
              -- a quoted scalar in KEY position: the scanner's `key` token precedes it (flow / block
              -- implicit keys) — does its run stay on one line (the lemma's `s'.line = sc.line`)?
              let isKey := i > 0 && (ts[i-1]!).val == .key
              if isKey then
                t := { t with keySites := t.keySites + 1 }
                if s'.line != st.line then t := { t with keyMultiLine := (s, tk.pos.offset) :: t.keyMultiLine }
              match scanNextToken_dispatchContent st q with
              | .ok s'' => if s''.tokens != s'.tokens then t := { t with dispBad := site :: t.dispBad }
              | .error _ => t := { t with dispBad := s!"{site}: dispatcher" :: t.dispBad }
          | _ => pure ()
  return t

def kindCount (t : Tally) (k : String) : Nat := (t.byKind.find? (·.1 == k)).map (·.2) |>.getD 0

def refusedWith (s : String) (p : ScanError → Bool) : Bool :=
  match scanFiltered s with
  | .error e => p e
  | .ok _ => false

end P102

section P102Test
open L4YAML.Proofs.Serialization.TokenEvents (go goOut tokenEvent tok)
open L4YAML.Proofs.Serialization.SerializationWellFormed (Event)

def testFlowBridge (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 102: S3 slice (3) first PR — flow indicators and quoted scalars as TraceOf leaves, before proof"
  let t := P102.tally P102.allRows
  let n := P102.kindCount t
  checkM state s!"P102(i) {t.rows} rows, {t.scanned} scanned, {t.refused} refused; [ {n "["} \{ {n "{"} ] {n "]"} } {n "}"} , {n ","} dq {n "dq"} sq {n "sq"}"
    (t.rows ≥ 600 && n "[" ≥ 60 && n "{" ≥ 40 && n "," ≥ 80 && n "dq" + n "sq" ≥ 60) ""
  checkM state s!"P102(ii) every flow indicator / quoted scalar token is silent (tokenEvent = none, goOut [tk] p = ([], p) from pending [] / [!a!] / [!b!, !a!]): {t.silentBad.length} bad"
    t.silentBad.isEmpty s!"{repr (t.silentBad.take 6)}"
  checkM state s!"P102(iii) '[' / '\{' direct (prior tokens seeded): {t.openRuns} runs, tokens = prefix.push the token at currentPos / one-char span / col+1 / flowLevel+1 / top pushed: {t.openBad.length} bad"
    (t.openBad.isEmpty && t.openRuns ≥ 100) s!"{repr (t.openBad.take 6)}"
  checkM state s!"P102(iv) ']' / '}' via dispatchFlowIndicators with the row's flow context: {t.closeRuns} runs, {t.closeRefused.length} refused, {t.closeBad.length} bad; level-0 / mismatched-top guards: {t.guardBad.length} not refused"
    (t.closeBad.isEmpty && t.closeRefused.isEmpty && t.guardBad.isEmpty && t.closeRuns ≥ 100)
    s!"{repr (t.closeBad.take 4)} {repr (t.closeRefused.take 4)} {repr (t.guardBad.take 4)}"
  checkM state s!"P102(v) ',' via dispatchFlowIndicators: {t.entryRuns} runs, {t.entryRefused.length} refused, {t.entryBad.length} bad"
    (t.entryBad.isEmpty && t.entryRefused.isEmpty && t.entryRuns ≥ 80) s!"{repr (t.entryBad.take 4)} {repr (t.entryRefused.take 4)}"
  checkM state s!"P102(vi) scanDoubleQuoted / scanSingleQuoted direct: {t.quotedRuns} runs, {t.quotedRefused.length} refused, {t.quotedBad.length} bad (token at currentPos, span quote-to-quote, peekBack = the quote)"
    (t.quotedBad.isEmpty && t.quotedRefused.isEmpty && t.quotedRuns ≥ 60) s!"{repr (t.quotedBad.take 4)} {repr (t.quotedRefused.take 4)}"
  checkM state s!"P102(vii) the dispatcher arms ('[' '\{' via dispatchFlowIndicators, quotes via dispatchContent) push the same tokens as the arm functions: {t.dispBad.length} bad"
    t.dispBad.isEmpty s!"{repr (t.dispBad.take 6)}"
  -- (viii) hand refuters
  checkM state "P102(viii) a bare ] / } / , at the top level is flowEndOutsideFlow"
    (["]", "}", ","].all (fun s => P102.refusedWith s (fun | .flowEndOutsideFlow .. => true | _ => false))) ""
  -- refuted prediction, pinned: a second closer after a closed collection is caught by the first
  -- close's validateFlowClose (trailingContent), never reaching the level-0 arm
  checkM state "P102(viii) [a]] / {a: b}} are trailingContent (the first close's validateFlowClose), not flowEndOutsideFlow"
    (["[a]]", "{a: b}}"].all (fun s => P102.refusedWith s (fun | .trailingContent .. => true | _ => false))) ""
  -- refuted prediction, pinned: in block context `]` `}` `,` are plain-scalar content (ns-plain-safe(block))
  checkM state "P102(viii) a] / a} / a, scan as ONE plain scalar (the indicator is plain content in block context)"
    (["a]", "a}", "a,"].all (fun s =>
      match scanFiltered s with
      | .ok ts => (ts.toList.filterMap (fun tk => match tk.val with | .scalar v .plain => some v | _ => none)) == [s]
      | .error _ => false)) ""
  checkM state "P102(viii) {a] / [a} are mismatchedFlowClose"
    (["{a]", "[a}"].all (fun s => P102.refusedWith s (fun | .mismatchedFlowClose .. => true | _ => false))) ""
  checkM state "P102(viii) unterminated / badly escaped quoted scalars are refused"
    (["\"abc", "'abc", "\"a\nb", "\"\\q\""].all (fun s => P102.refusedWith s (fun _ => true))) ""
  -- (x) quoted implicit keys: the key twins' one-line premise, and the scanner/grammar divergence
  checkM state s!"P102(x) quoted scalars in key position: {t.keySites} sites, {t.keyMultiLine.length} whose run leaves the line — exactly the multi-line quoted FLOW keys (accepted by the scanner AND the encoded grammar; the key twins' one-line premise fails there, the content twins at .flowIn serve): {repr t.keyMultiLine.reverse}"
    (t.keySites ≥ 15 && t.keyMultiLine.length == 4 &&
     t.keyMultiLine.reverse == [("{\"a\n b\": c}", 1), ("[\"a\n b\": c]", 1), ("{'a\n b': c}", 1), ("{'a': b, \"c\n d\": e}", 9)]) ""
  checkM state "P102(x) the block form \"a\n b\": c is refused (invalidImplicitKey) — the one-line rule the scanner enforces is the BLOCK implicit key's (inFlowCtx .blockKey = .flowKey is where the key twins apply)"
    (P102.refusedWith "\"a\n b\": c" (fun | .invalidImplicitKey .. => true | _ => false)) ""
  -- (ix) term-level instances
  checkM state "P102(ix) goOut [flowSequenceStart, flowEntry, flowSequenceEnd] [\"!e!\"] = ([], [\"!e!\"])"
    (goOut [tok .flowSequenceStart, tok .flowEntry, tok .flowSequenceEnd] ["!e!"] == ([], ["!e!"])) ""
  checkM state "P102(ix) tokenEvent (scalar \"a\" doubleQuoted) = none, (scalar \"a\" singleQuoted) = none"
    (tokenEvent (.scalar "a" .doubleQuoted) == none && tokenEvent (.scalar "a" .singleQuoted) == none) ""
  checkM state "P102(ix) go [flowMappingStart, scalar dq, flowMappingEnd, documentStart] [\"!a!\"] = [beginDocument, declareTag !a!]"
    (go [tok .flowMappingStart, tok (.scalar "a" .doubleQuoted), tok .flowMappingEnd, tok .documentStart] ["!a!"] ==
      [.beginDocument, .declareTag "!a!"]) ""

end P102Test

/-! ## Priority 103 — S3 slice (3) PR 2, PRICE: the flow frame census, before any re-walk is written

Item 464's NEXT.  The re-walk's carrier is a `TraceOf` twin of `StreamAccum.FlowOpenStack` (4 ctors)
over `SeqFrame` (9) / `MapFrame` (10) frames indexed by `FrameTail` (`sep` / `colon` / `question` /
`value`).  Before stating it: what frame shapes does scanner output actually show?  An executable walk
over the tokens — open pushes a frame at tail `sep`; `,` → `sep`; `.key` → `question`; `.value` →
`colon`; content or a nested open → `value`; close pops — censuses the (depth, tail) pairs at every
`,` / close / `.value`, and reads each closed frame's trace under the production `goOut`. -/
namespace P103
open L4YAML.Proofs.Serialization.TokenEvents (goOut tokenEvent)
open L4YAML.Proofs.Serialization.SerializationWellFormed (Event)

structure Frame where
  isSeq : Bool
  tail : String := "sep"
  entries : Nat := 0
  toks : List (Positioned YamlToken) := []
  shape : String := "betweenEmpty"   -- the SeqFrame / MapFrame constructor the walk is in
  propPending : Bool := false        -- an anchor / tag property awaits its content (one node, two tokens)

structure Tally where
  rows : Nat := 0
  scanned : Nat := 0
  frames : Nat := 0
  nested : Nat := 0
  maxDepth : Nat := 0
  closeAt : List (String × Nat) := []      -- (depth-tail, count)
  questionCloses : List String := []
  valueBad : List String := []
  traceBad : List String := []
  baseOpens : Nat := 0
  baseCloses : Nat := 0
  closeShape : List (String × Nat) := []   -- (depth:kind/shape, count)
  shapeBad : List String := []

/-- `SeqFrame` / `MapFrame` constructor transitions, read off the token kinds (`.key` from an explicit
    `?` vs. the simple-key insertion is told apart by the source char under the token). -/
def step (isSeq : Bool) (shape : String) (ev : String) : Option String :=
  let node := if isSeq then "midNode" else "midKey"
  match ev, shape with
  | "node", "betweenEmpty" | "node", "betweenHeld" => some node
  | "node", "midQuestion" => some "midExplicitKey"
  | "node", "midColon" | "node", "midExplicitColon" | "node", "midEmptyColon" | "node", "midQuestionEmptyColon" => some "betweenEntries"
  | "question", "betweenEmpty" | "question", "betweenHeld" => some "midQuestion"
  | "colon", "midNode" | "colon", "midKey" => some "midColon"
  | "colon", "midExplicitKey" => some "midExplicitColon"
  | "colon", "betweenEmpty" | "colon", "betweenHeld" => some "midEmptyColon"
  | "colon", "midQuestion" => some "midQuestionEmptyColon"
  | "comma", "betweenEmpty" => none
  | "comma", _ => some "betweenHeld"
  | _, _ => none

def tally (rows : List String) : Tally := Id.run do
  let mut t : Tally := {}
  for s in rows do
    t := { t with rows := t.rows + 1 }
    match scanFiltered s with
    | .error _ => pure ()
    | .ok ts =>
      t := { t with scanned := t.scanned + 1 }
      let mut st : List Frame := []
      for tk in ts do
        let depth := st.length
        -- record the token into every open frame (innermost owns it)
        st := st.map (fun f => { f with toks := tk :: f.toks })
        let isProp : Bool := match tk.val with | .anchor _ | .tag .. => true | _ => false
        let ev : String := match tk.val with
          | .flowSequenceStart | .flowMappingStart | .scalar .. | .alias _ | .anchor _ | .tag .. => "node"
          | .flowEntry => "comma"
          | .key => if String.Pos.Raw.get s ⟨tk.pos.offset⟩ == '?' then "question" else "key"
          | .value => "colon"
          | _ => ""
        if ev != "" && ev != "key" then
          match st with
          | f :: r =>
            if ev == "node" && f.propPending then
              st := { f with propPending := isProp } :: r     -- the property's own content: same node
            else
              match P103.step f.isSeq f.shape ev with
              | some sh => st := { f with shape := sh, propPending := isProp } :: r
              | none => t := { t with shapeBad := s!"{repr s}@{tk.pos.offset}: {f.shape} + {ev}" :: t.shapeBad }
          | [] => pure ()
        match tk.val with
        | .flowSequenceStart | .flowMappingStart =>
          if depth == 0 then t := { t with baseOpens := t.baseOpens + 1 }
          st := (match st with | f :: r => { f with tail := "value" } :: r | [] => [])
          st := { isSeq := tk.val == .flowSequenceStart, toks := [tk] } :: st
          t := { t with maxDepth := max t.maxDepth (depth + 1) }
        | .flowSequenceEnd | .flowMappingEnd =>
          match st with
          | f :: rest =>
            t := { t with frames := t.frames + 1, closeAt := P100.bump t.closeAt s!"{depth}:{f.tail}",
                          closeShape := P100.bump t.closeShape s!"{depth}:{if f.isSeq then "seq" else "map"}/{f.shape}" }
            if depth ≥ 2 then t := { t with nested := t.nested + 1 }
            if depth == 1 then t := { t with baseCloses := t.baseCloses + 1 }
            if f.tail == "question" then t := { t with questionCloses := s!"{repr s}@{tk.pos.offset}" :: t.questionCloses }
            let r := goOut f.toks.reverse ["!p!"]
            let onlyLeaf := r.1.all (fun e => match e with
              | .defineAnchor _ | .useAlias _ | .useTag _ => true | _ => false)
            if r.2 != ["!p!"] || !onlyLeaf then t := { t with traceBad := s!"{repr s}@{tk.pos.offset}" :: t.traceBad }
            st := (match rest with | g :: r' => { g with tail := "value" } :: r' | [] => [])
          | [] => pure ()
        | .flowEntry =>
          st := (match st with | f :: r => { f with tail := "sep", entries := f.entries + 1 } :: r | [] => [])
        | .key =>
          st := (match st with | f :: r => { f with tail := "question" } :: r | [] => [])
        | .value =>
          match st with
          | f :: r =>
            if f.tail != "value" && f.tail != "question" then t := { t with valueBad := s!"{repr s}@{tk.pos.offset}: {f.tail}" :: t.valueBad }
            st := { f with tail := "colon" } :: r
          | [] => pure ()
        | .scalar .. | .alias _ | .anchor _ | .tag .. =>
          st := (match st with | f :: r => { f with tail := "value" } :: r | [] => [])
        | _ => pure ()
  return t

def at_ (t : Tally) (k : String) : Nat := (t.closeAt.find? (·.1 == k)).map (·.2) |>.getD 0

end P103

section P103Test

def testFlowWalk (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 103: S3 slice (3) PR 2, PRICE — the flow frame census, before the re-walk"
  let t := P103.tally P102.allRows
  checkM state s!"P103(i) {t.rows} rows, {t.scanned} scanned: {t.frames} frames closed, {t.nested} nested, max depth {t.maxDepth}, base opens {t.baseOpens} = base closes {t.baseCloses}"
    (t.frames ≥ 150 && t.nested ≥ 30 && t.maxDepth == 4 && t.baseOpens == t.baseCloses) ""
  checkM state s!"P103(ii) closes by (depth:tail): {repr t.closeAt}; closes at tail `question`: {t.questionCloses.length}"
    (t.questionCloses.isEmpty && t.closeAt.all (fun p => !(p.1.endsWith ":question"))) s!"{repr (t.questionCloses.take 4)}"
  checkM state s!"P103(iii) every flow `.value` follows a key-shaped tail (value / question): {t.valueBad.length} bad"
    t.valueBad.isEmpty s!"{repr (t.valueBad.take 6)}"
  checkM state s!"P103(iv) every closed frame's token run under the production goOut keeps pending and emits only anchor / alias / tag events: {t.traceBad.length} bad"
    t.traceBad.isEmpty s!"{repr (t.traceBad.take 6)}"
  -- (v) the census by FRAME SHAPE (review on item 465: `[a]` closes `midNode`, `{a:}` closes `midColon`; the tail hides it)
  let sh (k : String) : Nat := (t.closeShape.filter (·.1.endsWith k)).foldl (· + ·.2) 0
  checkM state s!"P103(v) closes by (depth:kind/shape): {repr t.closeShape}; bad transitions {t.shapeBad.length}"
    (t.shapeBad.isEmpty && t.closeShape.foldl (· + ·.2) 0 == t.frames) s!"{repr (t.shapeBad.take 6)}"
  checkM state s!"P103(v) midNode+midKey {sh "/midNode" + sh "/midKey"}, betweenEntries {sh "/betweenEntries"}, betweenEmpty {sh "/betweenEmpty"}, betweenHeld {sh "/betweenHeld"}, midColon {sh "/midColon"}, midEmptyColon {sh "/midEmptyColon"}, midExplicitKey {sh "/midExplicitKey"}, midExplicitColon {sh "/midExplicitColon"}, midQuestion {sh "/midQuestion"}, midQuestionEmptyColon {sh "/midQuestionEmptyColon"}"
    (sh "/midNode" + sh "/midKey" ≥ 40 && sh "/betweenEntries" ≥ 40 && sh "/betweenEmpty" ≥ 5 && sh "/betweenHeld" ≥ 4 && sh "/midColon" ≥ 1) ""
  -- the reading pinned exactly (review on item 465: a predicted zero that is never asserted is no pin)
  checkM state "P103(v) exact: midNode 94 (1:76, 2:14, 3:4), midKey 5, betweenEntries 67, betweenEmpty 11, betweenHeld 4, midColon 1 ({a:}), midExplicitKey 1 ([? a]); midEmptyColon / midExplicitColon / midQuestion / midQuestionEmptyColon 0"
    (sh "/midNode" == 94 && P103.at_ { t with closeAt := t.closeShape } "1:seq/midNode" == 76 && sh "/midKey" == 5
      && sh "/betweenEntries" == 67 && sh "/betweenEmpty" == 11 && sh "/betweenHeld" == 4
      && sh "/midColon" == 1 && P103.at_ { t with closeAt := t.closeShape } "1:map/midColon" == 1
      && sh "/midExplicitKey" == 1 && P103.at_ { t with closeAt := t.closeShape } "1:seq/midExplicitKey" == 1
      && sh "/midEmptyColon" == 0 && sh "/midExplicitColon" == 0 && sh "/midQuestion" == 0 && sh "/midQuestionEmptyColon" == 0) ""
  -- the whole (depth : kind/shape) table, as a set (review: the label's depth split must be checked, not just quoted)
  let table : List (String × Nat) :=
    [("1:seq/midNode", 76), ("2:seq/midNode", 14), ("3:seq/midNode", 4), ("1:map/midKey", 5),
     ("1:seq/betweenEntries", 11), ("1:map/betweenEntries", 44), ("2:seq/betweenEntries", 1), ("2:map/betweenEntries", 8),
     ("3:map/betweenEntries", 2), ("4:map/betweenEntries", 1),
     ("1:seq/betweenEmpty", 3), ("1:map/betweenEmpty", 2), ("2:seq/betweenEmpty", 2), ("2:map/betweenEmpty", 1),
     ("3:seq/betweenEmpty", 1), ("4:seq/betweenEmpty", 1), ("4:map/betweenEmpty", 1),
     ("1:seq/betweenHeld", 2), ("1:map/betweenHeld", 2), ("1:map/midColon", 1), ("1:seq/midExplicitKey", 1)]
  checkM state s!"P103(v) the (depth:kind/shape) table is exactly the {table.length} pinned entries"
    (t.closeShape.length == table.length && table.all (fun e => t.closeShape.contains e))
    s!"got {repr t.closeShape}"

end P103Test

/-! ### Priority 104 (item 466, S3 slice (3) PR 2a): the frame algebra before proof.
`TraceOf/FlowWalk.lean`'s `TSeqFrame` / `TMapFrame` carry the frame's trace and claim the two
frame steps preserve it: `holdComma` (`,` on a non-`sep` tail) commits the open entry to the prefix,
`closeWithSep` lands every shape on `TFlowSequence` / `TFlowMapping` with the frame's trace.  The
executable mirror: the P103 shape walk, with per-frame token segments — `pref` (the committed
entries) and `entry` (since the last own `,`) — checked at every own `,` and every close for
(i) additivity `goOut frame p = pref ++ goOut entry p`, pending threaded, (ii) independence of the
pending list, (iii) the whole span's `tokenEvents` equal to the frame's trace, (iv) which of the
20 close arms / 16 `,` arms the rows reach, with rows added until every arm is; (v) hand-built
frames over abstract leaf premises, build-checked below. -/
namespace P104
open L4YAML.Proofs.Serialization.TokenEvents (goOut tokenEvents)
open L4YAML.Proofs.Serialization.SerializationWellFormed (Event)
open L4YAML.Proofs.Serialization.EventsOf (refLex eventsOfSegs)

structure Frame where
  isSeq : Bool
  shape : String := "betweenEmpty"
  toks : List (Positioned YamlToken) := []    -- reversed, opener inclusive
  entry : List (Positioned YamlToken) := []   -- reversed, the open entry since the last own `,`
  pref : List Event := []                     -- trace of the committed entries
  propPending : Bool := false
  openOff : Nat := 0                          -- byte offset of the opener

structure Tally where
  rows : Nat := 0
  scanned : Nat := 0
  steps : Nat := 0          -- own `,` + closes checked
  closes : Nat := 0
  addBad : List String := []
  indepBad : List String := []
  spanBad : List String := []
  shapeBad : List String := []
  closeArm : List (String × Nat) := []   -- kind/shape at `]` / `}`
  holdArm : List (String × Nat) := []    -- kind/shape at an own `,` with tl ≠ sep
  refusedOwn : List String := []
  -- (vi)–(viii): the lemmas' own premises / conclusions on the scanned spans (review on the
  -- first cut: (i)–(iv) compare `goOut` with `goOut`, a mirror, not the statements)
  closeTwinBad : List String := []   -- closeWithSep's conclusion: the closed span, standalone, scans to the frame trace
  closeRefBad : List String := []    -- … and the skeleton lexer (`refLex`, the grammar's executable twin) reads it the same
  holdTwinBad : List String := []    -- holdComma's conclusion: the held span + closer scans to the frame trace
  holdRefBad : List String := []     -- … and `refLex` agrees
  commaAtSep : List String := []     -- holdComma's premise `tl ≠ .sep`: own `,` reached on a `.sep` tail
  leadFreeBad : List String := []    -- closeLead's premise: a lead-free closer on a tail that is not `closeFree`
  holdSteps : Nat := 0
  aliasOut : List String := []       -- the scanner twin's `undefinedAlias` on a span whose anchor sits outside it (not grammar)

/-- Rows aimed at the shapes P103's census never closed or held: explicit `?`, empty keys, `[a:]`,
    bare `{a}`, each closed and each followed by `,`. -/
def own : List String :=
  ["[? a:]", "[:]", "[? ]", "[? :]", "{:}", "{? }", "{? :}", "{? a}", "{? a:}", "[a:]", "{a}",
   "[? a: b]", "{? a: b}", "[? a:, b]", "[:, a]", "[? , a]", "[? :, a]", "{:, a: b}", "{? , a: b}",
   "{? :, a: b}", "{? a, b: c}", "{? a:, b: c}", "[a:, b]", "{a, b}", "{a:, b}", "[? a, b]",
   "[a, b]", "{a: b, c: d}", "[[a], b]", "{a: {b: c}, d: e}", "[? a: b, c: d]", "{? a: b, c: d}",
   "[&x a, *x]", "{!t a: &y b, *y: c}", "[\"a\": b]", "{\"a\": b, 'c': d}"]
def allRows : List String := (P102.allRows ++ own).eraseDups
def pendings : List (List String) := [[], ["!a!"], ["!b!", "!a!"]]
def isSep (sh : String) : Bool := sh == "betweenEmpty" || sh == "betweenHeld"
/-- The `FrameTail` a shape sits at (`TSeqFrame` / `TMapFrame`'s tail index). -/
def tailOf (sh : String) : String :=
  if isSep sh then "sep"
  else if sh == "midNode" || sh == "midKey" || sh == "midExplicitKey" then "value"
  else if sh == "midQuestion" then "question" else "colon"
def isWs (ch : Char) : Bool := ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r'
/-- The lemma conclusion's executable twin on a span: standalone, the scanner accepts it with
    `tokenEvents` = `ev`, and `refLex` reads `ev` too.  Returns (scanner twin ok, refLex twin ok). -/
def twin (sub : String) (ev : List Event) : Bool × Bool :=
  (((scanFiltered sub).toOption.map tokenEvents) == some ev, ((refLex sub).map eventsOfSegs) == some ev)
/-- The scanner refused the span for an alias whose anchor sits outside it — a semantic check
    (`undefinedAlias`), not a grammar reading; the span's grammar twin is `refLex` alone there. -/
def aliasOutside (sub : String) : Bool :=
  match scanFiltered sub with
  | .error (.undefinedAlias ..) => true
  | _ => false

def tally (rows : List String) : Tally := Id.run do
  let mut t : Tally := {}
  for s in rows do
    t := { t with rows := t.rows + 1 }
    match scanFiltered s with
    | .error _ => if own.contains s then t := { t with refusedOwn := s :: t.refusedOwn }
    | .ok ts =>
      t := { t with scanned := t.scanned + 1 }
      let mut st : List Frame := []
      for tk in ts do
        st := st.map (fun f => { f with toks := tk :: f.toks, entry := tk :: f.entry })
        let isProp : Bool := match tk.val with | .anchor _ | .tag .. => true | _ => false
        let ev : String := match tk.val with
          | .flowSequenceStart | .flowMappingStart | .scalar .. | .alias _ | .anchor _ | .tag .. => "node"
          | .flowEntry => "comma"
          | .key => if String.Pos.Raw.get s ⟨tk.pos.offset⟩ == '?' then "question" else "key"
          | .value => "colon"
          | _ => ""
        -- the frame step checks, BEFORE the shape moves
        let stepCheck : Frame → String → Tally := fun f site => Id.run do
          let mut t' := { t with steps := t.steps + 1 }
          let base := (goOut f.toks.reverse []).1
          for p in pendings do
            let r := goOut f.toks.reverse p
            let e := goOut f.entry.reverse p
            if r.1 != f.pref ++ e.1 || r.2 != p then
              t' := { t' with addBad := s!"{repr s}@{tk.pos.offset} {site} p={p}" :: t'.addBad }
            if r.1 != base then
              t' := { t' with indepBad := s!"{repr s}@{tk.pos.offset} {site} p={p}" :: t'.indepBad }
          return t'
        match tk.val with
        | .flowEntry =>
          match st with
          | f :: r =>
            t := stepCheck f "comma"
            if !isSep f.shape then
              t := { t with holdArm := P100.bump t.holdArm s!"{if f.isSeq then "seq" else "map"}/{f.shape}", holdSteps := t.holdSteps + 1 }
              let sub := (String.Pos.Raw.extract s ⟨f.openOff⟩ ⟨tk.pos.offset + 1⟩) ++ (if f.isSeq then "]" else "}")
              let (a, b) := twin sub (goOut f.toks.reverse []).1
              if !a then t := { t with holdTwinBad := s!"{repr s}@{tk.pos.offset} {sub}" :: t.holdTwinBad }
              if !b then t := { t with holdRefBad := s!"{repr s}@{tk.pos.offset} {sub}" :: t.holdRefBad }
            else
              t := { t with commaAtSep := s!"{repr s}@{tk.pos.offset} {f.shape}" :: t.commaAtSep }
            st := { f with entry := [], pref := f.pref ++ (goOut f.entry.reverse []).1 } :: r
          | [] => pure ()
        | .flowSequenceEnd | .flowMappingEnd =>
          match st with
          | f :: rest =>
            t := stepCheck f "close"
            t := { t with closes := t.closes + 1,
                          closeArm := P100.bump t.closeArm s!"{if f.isSeq then "seq" else "map"}/{f.shape}" }
            if tokenEvents f.toks.reverse.toArray != (goOut f.toks.reverse []).1 then
              t := { t with spanBad := s!"{repr s}@{tk.pos.offset}" :: t.spanBad }
            let sub := String.Pos.Raw.extract s ⟨f.openOff⟩ ⟨tk.pos.offset + 1⟩
            let (a, b) := twin sub (goOut f.toks.reverse []).1
            if !a then
              if aliasOutside sub then t := { t with aliasOut := s!"{repr s}@{tk.pos.offset} {sub}" :: t.aliasOut }
              else t := { t with closeTwinBad := s!"{repr s}@{tk.pos.offset} {sub}" :: t.closeTwinBad }
            if !b then t := { t with closeRefBad := s!"{repr s}@{tk.pos.offset} {sub}" :: t.closeRefBad }
            if tk.pos.offset > 0 && !isWs (String.Pos.Raw.get s ⟨tk.pos.offset - 1⟩) && tailOf f.shape == "question" then
              t := { t with leadFreeBad := s!"{repr s}@{tk.pos.offset} {f.shape}" :: t.leadFreeBad }
            st := rest
          | [] => pure ()
        | _ => pure ()
        -- the shape walk (P103's), on the frame that now holds the token
        if ev != "" && ev != "key" && ev != "comma" then
          match st with
          | f :: r =>
            if ev == "node" && f.propPending then
              st := { f with propPending := isProp } :: r
            else
              match P103.step f.isSeq f.shape ev with
              | some sh => st := { f with shape := sh, propPending := isProp } :: r
              | none => t := { t with shapeBad := s!"{repr s}@{tk.pos.offset}: {f.shape} + {ev}" :: t.shapeBad }
          | [] => pure ()
        else if ev == "comma" then
          st := (match st with | f :: r => { f with shape := "betweenHeld" } :: r | [] => [])
        match tk.val with
        | .flowSequenceStart | .flowMappingStart =>
          st := { isSeq := tk.val == .flowSequenceStart, toks := [tk], entry := [tk], openOff := tk.pos.offset } :: st
        | _ => pure ()
  return t
def arms (l : List (String × Nat)) : Nat := l.length
end P104

section P104Test
open L4YAML.Proofs.Serialization.SerializationWellFormed (Event)

def testFlowAlgebra (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 104: S3 slice (3) PR 2a — the frame algebra (TSeqFrame / TMapFrame trace steps), before proof"
  let t := P104.tally P104.allRows
  checkM state s!"P104(i) {t.rows} rows, {t.scanned} scanned, {t.steps} frame steps, {t.closes} closes; additivity bad {t.addBad.length}"
    (t.rows ≥ 670 && t.steps ≥ 264 && t.closes ≥ 183 && t.addBad.isEmpty) s!"{t.addBad.take 5}"
  checkM state s!"P104(ii) trace independent of the pending list: bad {t.indepBad.length}" t.indepBad.isEmpty s!"{t.indepBad.take 5}"
  checkM state s!"P104(iii) whole-span tokenEvents = frame trace: bad {t.spanBad.length}" t.spanBad.isEmpty s!"{t.spanBad.take 5}"
  checkM state s!"P104(iv) close arms reached {P104.arms t.closeArm}/20, hold arms {P104.arms t.holdArm}/16: {t.closeArm} | {t.holdArm}"
    (P104.arms t.closeArm == 20 && P104.arms t.holdArm == 16) ""
  -- P5 REFUTED on one row: `*y: c` — the alias arm reads `y:` as the anchor name (YAML's own
  -- gotcha: `:` is an anchor character), so the mapping has no `:` and the scanner refuses it.
  -- Pinned exactly; the arm census above is 20/20 and 16/16 without it.
  checkM state s!"P104(iv') own rows refused by the scanner: exactly the alias-key row {t.refusedOwn}"
    (t.refusedOwn == ["{!t a: &y b, *y: c}"]) ""
  checkM state s!"P104(iv'') shape walk: bad transitions {t.shapeBad.length}" t.shapeBad.isEmpty s!"{t.shapeBad.take 5}"
  -- (vi)–(viii) the statements themselves on the scanned spans (review on the first cut)
  checkM state s!"P104(vi) closeWithSep's conclusion on every closed span, standalone: scanner twin bad {t.closeTwinBad.length}, refLex twin bad {t.closeRefBad.length} over {t.closes} closes; anchor outside the span (scanner `undefinedAlias`, refLex read): {t.aliasOut.length}"
    (t.closeTwinBad.isEmpty && t.closeRefBad.isEmpty && t.aliasOut.length == 3) s!"{t.closeTwinBad} | {t.closeRefBad} | {t.aliasOut}"
  checkM state s!"P104(vii) holdComma's conclusion on every held span + closer: scanner twin bad {t.holdTwinBad.length}, refLex twin bad {t.holdRefBad.length} over {t.holdSteps} holds; `,` on a `.sep` tail: {t.commaAtSep.length}"
    (t.holdTwinBad.isEmpty && t.holdRefBad.isEmpty && t.commaAtSep.isEmpty) s!"{t.holdTwinBad} | {t.holdRefBad} | {t.commaAtSep}"
  checkM state s!"P104(viii) closeLead's premise: lead-free closers on a non-closeFree (`question`) tail: {t.leadFreeBad.length}"
    t.leadFreeBad.isEmpty s!"{t.leadFreeBad.take 4}"
end P104Test

section P104Examples
open L4YAML.Surface L4YAML.Proofs.Serialization.TraceOf L4YAML.Proofs.Serialization.TraceOf.FlowWalk
open L4YAML.Proofs.Serialization.SerializationWellFormed (Event)
open L4YAML.Proofs.StreamAccum (FrameTail)
variable {n : Nat} {c : YamlContext}
-- `[]`
example (sp : SurfPos) : TSeqFrame n c .sep sp sp [] := .betweenEmpty sp
-- `[a` (midNode), `[a]` is its close
example {sp sp' : SurfPos} {ev : List Event} (h : TFlowNode n c sp sp' ev) :
    TSeqFrame n c (.value false) sp sp' ([] ++ ev) :=
  .midNode false sp sp sp' [] ev (.init sp) h (fun h => nomatch h)
-- `[a,`
example {sp sp_e sp_c : SurfPos} {ev : List Event} (h : TFlowNode n c sp sp_e ev) (hc : GLit ',' sp_e sp_c) :
    TSeqFrame n c .sep sp sp_c ev :=
  .betweenHeld sp sp_e sp_c sp_c ev (.single n c sp sp_e sp_e ev (.node n c sp sp_e ev h) (.none sp_e))
    (.single (.node n c sp sp_e ev h) (.none sp_e)) hc (.none sp_c)
-- `[a, b`
example {sp s₁ s₂ s₃ sp' : SurfPos} {ev1 ev2 : List Event} (h1 : TFlowNode n c sp s₁ ev1) (hc : GLit ',' s₁ s₂)
    (hs : SSeparate n c s₂ s₃) (h2 : TFlowNode n c s₃ sp' ev2) :
    TSeqFrame n c (.value false) sp sp' (ev1 ++ ev2) :=
  .betweenEntries false sp sp' (ev1 ++ ev2)
    (.consMore n c sp s₁ s₁ s₂ s₃ sp' ev1 ev2 (.node n c sp s₁ ev1 h1) (.none s₁) hc (.some _ _ hs)
      (.single n c s₃ sp' sp' ev2 (.node n c s₃ sp' ev2 h2) (.none sp')))
    (.consMore (.node n c sp s₁ ev1 h1) (.none s₁) hc (.some _ _ hs)
      (.single n c s₃ sp' sp' ev2 (.node n c s₃ sp' ev2 h2) (.none sp'))
      (.single (.node n c s₃ sp' ev2 h2) (.none sp')))
-- `[a:`
example {sp sp_k sp' : SurfPos} {ev : List Event} (h : TFlowNode n c sp sp_k ev) (hcol : GLit ':' sp_k sp') :
    TSeqFrame n c (.colon false) sp sp' ([] ++ ev) :=
  .midColon false sp sp sp_k sp_k sp' [] ev (.init sp) h (fun h => nomatch h) (.none sp_k) hcol
-- `[? a`
example {sp sp_qe sp_k0 sp' : SurfPos} {ev : List Event} (hq : GLit '?' sp sp_qe) (hs : SSeparate n c sp_qe sp_k0)
    (h : TFlowNode n c sp_k0 sp' ev) : TSeqFrame n c (.value false) sp sp' ([] ++ ev) :=
  .midExplicitKey false sp sp sp_qe sp_k0 sp' [] ev (.init sp) hq hs h (fun h => nomatch h)
-- `[:`
example {sp sp' : SurfPos} (hcol : GLit ':' sp sp') : TSeqFrame n c (.colon false) sp sp' [] :=
  .midEmptyColon sp sp sp' [] (.init sp) hcol
-- `[? :`
example {sp sp_qe sp_s sp' : SurfPos} (hq : GLit '?' sp sp_qe) (hs : SSeparate n c sp_qe sp_s) (hcol : GLit ':' sp_s sp') :
    TSeqFrame n c (.colon false) sp sp' [] :=
  .midQuestionEmptyColon sp sp sp_qe sp_s sp' [] (.init sp) hq hs hcol
-- `{a` (midKey), `{a:` (midColon), `{? ` (midQuestion), `{? :`
example {sp sp' : SurfPos} {ev : List Event} (h : TFlowNode n c sp sp' ev) (hj : TCFlowJsonNode n c sp sp' ev) :
    TMapFrame n c (.value true) sp sp' ([] ++ ev) :=
  .midKey true sp sp sp' [] ev (.init sp) h (fun _ => hj)
example {sp sp' : SurfPos} {ev : List Event} (h : TFlowNode n c sp sp' ev) :
    TMapFrame n c (.value false) sp sp' ([] ++ ev) :=
  .midKey false sp sp sp' [] ev (.init sp) h (fun h => nomatch h)
example {sp sp_k sp' : SurfPos} {ev : List Event} (h : TFlowNode n c sp sp_k ev) (hcol : GLit ':' sp_k sp') :
    TMapFrame n c (.colon false) sp sp' ([] ++ ev) :=
  .midColon false sp sp sp_k sp_k sp' [] ev (.init sp) h (fun h => nomatch h) (.none sp_k) hcol
example {sp sp' : SurfPos} (hq : GLit '?' sp sp') : TMapFrame n c .question sp sp' [] :=
  .midQuestion sp sp sp' [] (.init sp) hq
example {sp sp_qe sp_s sp' : SurfPos} (hq : GLit '?' sp sp_qe) (hs : SSeparate n c sp_qe sp_s) (hcol : GLit ':' sp_s sp') :
    TMapFrame n c (.colon false) sp sp' [] :=
  .midQuestionEmptyColon sp sp sp_qe sp_s sp' [] (.init sp) hq hs hcol
-- stack shapes: depth 0 (`nil`); a base opener after a gap (`sp_before ≠ sp_br`);
-- `[[` (parent at `.sep`) and `{a: [` (parent at `.colon false`)
example (sp : SurfPos) (tl : FrameTail) : TFlowStackB n 0 #[] tl sp sp [] := .nil sp tl
example {sp_before sp_br sp_open : SurfPos} (ho : GLit '[' sp_br sp_open) :
    TFlowOpenStack n 1 #[true] .sep sp_before sp_open [] :=
  .seqBase sp_before sp_br sp_open sp_open sp_open .sep [] ho (.none sp_open) (.betweenEmpty sp_open)
example {sp_br sp_o1 sp_o2 : SurfPos} (h1 : GLit '[' sp_br sp_o1) (h2 : GLit '[' sp_o1 sp_o2) :
    TFlowOpenStack n 2 (#[true].push true) .sep sp_br sp_o2 ([] ++ []) :=
  .seqNest 1 #[true] .sep .sep sp_br sp_o1 sp_o1 sp_o2 sp_o2 sp_o2 [] []
    (.seqBase sp_br sp_br sp_o1 sp_o1 sp_o1 .sep [] h1 (.none sp_o1) (.betweenEmpty sp_o1))
    (fun _ h => nomatch h) (.inr ⟨rfl, rfl⟩) h2 (.none sp_o2) (.betweenEmpty sp_o2)
example {sp_br sp_o1 sp_k sp_c sp_b sp_o2 : SurfPos} {ev : List Event} (h1 : GLit '{' sp_br sp_o1)
    (hk : TFlowNode n (inFlowCtx .flowOut) sp_o1 sp_k ev) (hc : GLit ':' sp_k sp_c) (hs : SSeparateLines n sp_c sp_b)
    (h2 : GLit '[' sp_b sp_o2) :
    TFlowOpenStack n 2 (#[false].push true) .sep sp_br sp_o2 (([] ++ ev) ++ []) :=
  .seqNest 1 #[false] (.colon false) .sep sp_br sp_c sp_b sp_o2 sp_o2 sp_o2 ([] ++ ev) []
    (.mapBase sp_br sp_br sp_o1 sp_o1 sp_c (.colon false) ([] ++ ev) h1 (.none sp_o1)
      (.midColon false sp_o1 sp_o1 sp_k sp_k sp_c [] ev (.init sp_o1) hk (fun h => nomatch h) (.none sp_k) hc))
    (fun _ h => nomatch h) (.inl hs) h2 (.none sp_o2) (.betweenEmpty sp_o2)
end P104Examples

/-! ### Priority 105 — S3 slice (3) PR 2b-i: the stack-level receive twins (item 467), before proof

    The S side moves an open frame on a node / `?` / `:` through ten `FlowOpenStack.receive*`
    lemmas; the T twins (`TFlowOpenStack.receive*`, `TraceOf/FlowWalk` §6) must grow the frame's
    trace by exactly the node's events.  Rule 2 here: at every such step of every frame over the
    P104 rows (plus rows for the property-run shapes), BEFORE the shape moves, (a) the lemma each
    step would spend, by (tail, token, props held, node had props); (b) its PREMISES — a node never
    lands on a `.value` tail (`h_tail`), `?` only on `.sep`, `:` only on `.sep` / `.question` /
    a mid `.value`, a glued token only after a `leadFree` tail (`h_lead`); (c) its CONCLUSION's
    executable twin — the span from the opener through the token, closed, standalone, scans
    (`tokenEvents`) and lexes (`refLex`) to the frame's trace so far.  A nested open is a node of
    the PARENT; its twin is read when the nested frame closes. -/
namespace P105
open L4YAML.Proofs.Serialization.TokenEvents (goOut tokenEvents)
open L4YAML.Proofs.Serialization.SerializationWellFormed (Event)
open L4YAML.Proofs.Serialization.EventsOf (refLex eventsOfSegs)

structure Frame where
  isSeq : Bool
  shape : String := "betweenEmpty"
  toks : List (Positioned YamlToken) := []    -- reversed, opener inclusive
  propPending : Bool := false                 -- a `[96]` run is held, no content yet
  nodeProps : Bool := false                   -- the node that made this tail carried properties
  kj : Bool := false                          -- the tail's JSON bit
  openOff : Nat := 0

structure Tally where
  rows : Nat := 0
  scanned : Nat := 0
  steps : Nat := 0                            -- receive steps (twin read)
  arm : List (String × Nat) := []             -- the S lemma each step spends
  nodeAtValue : List String := []             -- `receiveNode.h_tail`: a node on a `.value` tail
  questionOff : List String := []             -- `receiveQuestion.h_tail`: `?` off `.sep`
  colonBad : List String := []                -- `:` on `.colon` / `betweenEntries`
  glueBad : List String := []                 -- a glued token after a non-`leadFree` tail
  twinBad : List String := []                 -- scanner twin of the conclusion
  refBad : List String := []                  -- refLex twin of the conclusion
  aliasOut : List String := []                -- scanner `undefinedAlias`: anchor outside the cut
  refusedOwn : List String := []

/-- Rows for the property-run shapes the receive lemmas name (`[&a]`, `[&a b]`, `[&a : b]`,
    `[? &a : b]`, `[a, &x b : c]`, …) and the glued JSON forms. -/
def own : List String :=
  ["[&a]", "[&a, b]", "{&a: v}", "[&a b]", "[&a [b]]", "[&a : b]", "[a, &x : b]", "{&a : b}",
   "[&a !t : b]", "[? &a : b]", "{? &a : b}", "[a, &x b : c]", "[!t a]", "[&a !t b]", "[? a : b]",
   "{? a : b}", "[\"a\":b]", "{\"a\":b}", "[&a b, c]", "{&a b: c}"]
def allRows : List String := (P104.allRows ++ own).eraseDups
def tailOf (sh : String) : String := P104.tailOf sh
def leadFree (f : Frame) : Bool :=
  match tailOf f.shape with
  | "sep" | "value" => true
  | "colon" => f.kj
  | _ => false
def isWs (ch : Char) : Bool := ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r'
def rstrip (x : String) : String := String.ofList (x.toList.reverse.dropWhile isWs).reverse
/-- The receive lemma a step spends, or `none` for a property token (the run is held, no step). -/
def armOf (f : Frame) (ev : String) (isProp : Bool) : Option String :=
  let tl := tailOf f.shape
  match ev with
  | "node" => if isProp then none else some (if f.propPending then "receivePropsContent" else "receiveNode")
  | "question" => some "receiveQuestion"
  | "colon" =>
    some (if tl == "sep" then (if f.propPending then "receiveColonPropsSep" else "receiveColonSep")
      else if tl == "question" then (if f.propPending then "receiveColonPropsQuestion" else "receiveColonQuestion")
      else if f.nodeProps then "receivePropsNodeColon" else "receiveNodeColon")
  | _ => none

def tally (rows : List String) : Tally := Id.run do
  let mut t : Tally := {}
  for s in rows do
    t := { t with rows := t.rows + 1 }
    match scanFiltered s with
    | .error _ => if own.contains s then t := { t with refusedOwn := s :: t.refusedOwn }
    | .ok ts =>
      t := { t with scanned := t.scanned + 1 }
      let mut st : List Frame := []
      for i in [0:ts.size] do
        let tk := ts[i]!
        st := st.map (fun f => { f with toks := tk :: f.toks })
        let endOff := if i + 1 < ts.size then ts[i + 1]!.pos.offset else s.utf8ByteSize
        let isProp : Bool := match tk.val with | .anchor _ | .tag .. => true | _ => false
        let isJson : Bool := match tk.val with
          | .scalar _ .doubleQuoted | .scalar _ .singleQuoted | .flowSequenceStart | .flowMappingStart => true
          | _ => false
        let ev : String := match tk.val with
          | .flowSequenceStart | .flowMappingStart | .scalar .. | .alias _ | .anchor _ | .tag .. => "node"
          | .flowEntry => "comma"
          | .key => if String.Pos.Raw.get s ⟨tk.pos.offset⟩ == '?' then "question" else "key"
          | .value => "colon"
          | _ => ""
        let glued := tk.pos.offset > 0 && !isWs (String.Pos.Raw.get s ⟨tk.pos.offset - 1⟩)
        -- the conclusion's twin on a frame: its span through `endOff`, closed on a fresh line
        let twinOn : Frame → Nat → String → Tally → Tally := fun f e site t' => Id.run do
          let sub := rstrip (String.Pos.Raw.extract s ⟨f.openOff⟩ ⟨e⟩) ++ "\n" ++ (if f.isSeq then "]" else "}")
          let ev := (goOut f.toks.reverse []).1
          let (a, b) := P104.twin sub ev
          let mut t'' := { t' with steps := t'.steps + 1 }
          if !a then
            if P104.aliasOutside sub then t'' := { t'' with aliasOut := s!"{repr s}@{tk.pos.offset} {site}" :: t''.aliasOut }
            else t'' := { t'' with twinBad := s!"{repr s}@{tk.pos.offset} {site} {repr sub}" :: t''.twinBad }
          if !b then t'' := { t'' with refBad := s!"{repr s}@{tk.pos.offset} {site} {repr sub}" :: t''.refBad }
          return t''
        -- (a)/(b)/(c) on the frame that receives the token, BEFORE the shape moves
        if ev == "node" || ev == "question" || ev == "colon" then
          match st with
          | f :: _ =>
            let tl := tailOf f.shape
            let here := s!"{repr s}@{tk.pos.offset} {f.shape}+{ev}"
            if ev == "node" && tl == "value" then t := { t with nodeAtValue := here :: t.nodeAtValue }
            if ev == "question" && tl != "sep" then t := { t with questionOff := here :: t.questionOff }
            if ev == "colon" && (tl == "colon" || f.shape == "betweenEntries") then t := { t with colonBad := here :: t.colonBad }
            if glued && ev != "colon" && !leadFree f then t := { t with glueBad := here :: t.glueBad }
            match armOf f ev isProp with
            | some a =>
              t := { t with arm := P100.bump t.arm a }
              -- a nested open's twin is read at its close (below); every other step's here
              if !(tk.val == .flowSequenceStart || tk.val == .flowMappingStart) then t := twinOn f endOff a t
            | none => pure ()
          | [] => pure ()
        -- `,` / close with a held run: the run decorated an EMPTY node (`receivePropsEmpty`); its
        -- conclusion's twin is the span through the run (this token's start), closed (review, round 1)
        if ev == "comma" || tk.val == .flowSequenceEnd || tk.val == .flowMappingEnd then
          match st with
          | f :: _ =>
            if f.propPending then
              t := { t with arm := P100.bump t.arm "receivePropsEmpty" }
              t := twinOn f tk.pos.offset "receivePropsEmpty" t
          | [] => pure ()
        -- the shape walk (P103's), on the frame that now holds the token
        if ev != "" && ev != "key" && ev != "comma" then
          match st with
          | f :: r =>
            if ev == "node" && isProp then
              st := { f with propPending := true } :: r
            else
              match P103.step f.isSeq f.shape ev with
              | some sh =>
                let kjNode := ev == "node" && isJson
                st := { f with shape := sh, propPending := false,
                               nodeProps := if ev == "node" then f.propPending else f.nodeProps,
                               kj := if ev == "node" then kjNode else f.kj } :: r
              | none => pure ()
          | [] => pure ()
        else if ev == "comma" then
          st := (match st with | f :: r => { f with shape := "betweenHeld", propPending := false } :: r | [] => [])
        match tk.val with
        | .flowSequenceStart | .flowMappingStart =>
          st := { isSeq := tk.val == .flowSequenceStart, toks := [tk], openOff := tk.pos.offset } :: st
        | .flowSequenceEnd | .flowMappingEnd =>
          match st with
          | _ :: (p :: r) =>
            -- the parent received the nested node: read its twin now, through the closer
            t := twinOn p (tk.pos.offset + 1) "receiveNode(nested)" t
            st := { p with shape := p.shape, propPending := false } :: r
          | _ :: [] => st := []
          | [] => pure ()
        | _ => pure ()
  return t
end P105

section P105Test
def testFlowReceive (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 105: S3 slice (3) PR 2b-i — the receive twins (TFlowOpenStack.receive*), before proof"
  let t := P105.tally P105.allRows
  -- P1 HELD (10/10 arms); pinned exactly — the arm table is the roster PR 2b-ii/iii re-walk
  checkM state s!"P105(i) {t.rows} rows, {t.scanned} scanned, {t.steps} receive steps; arms {t.arm}"
    (t.rows == 693 && t.scanned == 540 && t.steps == 562 &&
      t.arm.mergeSort (fun a b => a.1 ≤ b.1) ==
        [("receiveColonPropsQuestion", 2), ("receiveColonPropsSep", 4), ("receiveColonQuestion", 4),
         ("receiveColonSep", 8), ("receiveNode", 365), ("receiveNodeColon", 101), ("receivePropsContent", 38),
         ("receivePropsEmpty", 6), ("receivePropsNodeColon", 7), ("receiveQuestion", 27)]) s!"{t.arm}"
  checkM state s!"P105(ii) premises: node on a `.value` tail {t.nodeAtValue.length}, `?` off `.sep` {t.questionOff.length}, `:` on `.colon`/betweenEntries {t.colonBad.length}, glued after a non-leadFree tail {t.glueBad.length}"
    (t.nodeAtValue.isEmpty && t.questionOff.isEmpty && t.colonBad.isEmpty && t.glueBad.isEmpty)
    s!"{t.nodeAtValue.take 4} | {t.questionOff.take 4} | {t.colonBad.take 4} | {t.glueBad.take 4}"
  checkM state s!"P105(iii) conclusions: scanner twin bad {t.twinBad.length}, refLex twin bad {t.refBad.length}; anchor outside the cut {t.aliasOut.length}"
    -- P3's alias count REFUTED (4 predicted, 3 read): `[&x [*x]]`'s outer cut `[&x [*x]` CARRIES its
    -- anchor, so only the three cuts that start after their anchor are scanner-refused
    (t.twinBad.isEmpty && t.refBad.isEmpty && t.aliasOut.length == 3) s!"{t.twinBad.take 6} | {t.refBad.take 6} | {t.aliasOut}"
  checkM state s!"P105(iv) own rows refused: {t.refusedOwn}" t.refusedOwn.isEmpty ""
end P105Test

section P105Examples
open L4YAML.Surface L4YAML.Proofs.Serialization.TraceOf L4YAML.Proofs.Serialization.TraceOf.FlowWalk
open L4YAML.Proofs.Serialization.SerializationWellFormed (Event)
open L4YAML.Proofs.StreamAccum (FrameTail)
variable {n : Nat}
/-! Hand-built receive chains over abstract leaf premises, one per receive twin (elaborated by
    the build): the trace index of each conclusion is the frame's trace so far. -/
-- depth-0 open: `[` / `{`
example {sp_br sp_o : SurfPos} (ho : GLit '[' sp_br sp_o) : TFlowStackB n 1 #[true] .sep sp_br sp_o [] :=
  TFlowStackB.openSeqBase ho (.none sp_o)
example {sp_br sp_o : SurfPos} (ho : GLit '{' sp_br sp_o) : TFlowStackB n 1 #[false] .sep sp_br sp_o [] :=
  TFlowStackB.openMapBase ho (.none sp_o)
-- `[a`: the node glued to `[` (`.sep` is leadFree) — receiveNode
example {sp_br sp_o sp_a : SurfPos} {ev : List Event} (ho : GLit '[' sp_br sp_o)
    (ha : TFlowNode n .flowIn sp_o sp_a ev) :
    TFlowOpenStack n 1 #[true] (.value false) sp_br sp_a ([] ++ ev) :=
  (TFlowOpenStack.seqBase sp_br sp_br sp_o sp_o sp_o .sep [] ho (.none sp_o) (.betweenEmpty sp_o)).receiveNode
    (fun _ h => nomatch h) (.inr ⟨rfl, rfl⟩) ha (fun h => nomatch h)
-- `{a: b` — receiveNodeColon then receiveNode after a separation
example {sp_br sp_o sp_a sp_c sp_s sp_b : SurfPos} {ev_a ev_b : List Event} (ho : GLit '{' sp_br sp_o)
    (ha : TFlowNode n .flowIn sp_o sp_a ev_a) (hc : GLit ':' sp_a sp_c) (hs : SSeparateLines n sp_c sp_s)
    (hb : TFlowNode n .flowIn sp_s sp_b ev_b) :
    TFlowOpenStack n 1 #[false] (.value false) sp_br sp_b (([] ++ ev_a) ++ ev_b) :=
  ((TFlowOpenStack.mapBase sp_br sp_br sp_o sp_o sp_o .sep [] ho (.none sp_o) (.betweenEmpty sp_o)).receiveNodeColon
      (kj := false) (.inl rfl) (.inr ⟨rfl, rfl⟩) ha (fun h => nomatch h) (.inr rfl) hc).receiveNode
    (fun _ h => nomatch h) (.inl hs) hb (fun h => nomatch h)
-- `{"a":b` — a JSON key, the value glued to the `:` ([149]; `.colon true` is leadFree)
example {sp_br sp_o sp_a sp_c sp_b : SurfPos} {ev_a ev_b : List Event} (ho : GLit '{' sp_br sp_o)
    (ha : TFlowNode n .flowIn sp_o sp_a ev_a) (hj : TCFlowJsonNode n .flowIn sp_o sp_a ev_a) (hc : GLit ':' sp_a sp_c)
    (hb : TFlowNode n .flowIn sp_c sp_b ev_b) :
    TFlowOpenStack n 1 #[false] (.value false) sp_br sp_b (([] ++ ev_a) ++ ev_b) :=
  ((TFlowOpenStack.mapBase sp_br sp_br sp_o sp_o sp_o .sep [] ho (.none sp_o) (.betweenEmpty sp_o)).receiveNodeColon
      (kj := true) (.inl rfl) (.inr ⟨rfl, rfl⟩) ha (fun _ => hj) (.inr rfl) hc).receiveNode
    (fun _ h => nomatch h) (.inr ⟨rfl, rfl⟩) hb (fun h => nomatch h)
-- `[? a : b` — receiveQuestion, receiveNodeColon on `.question`, receiveNode
example {sp_br sp_o sp_q sp_s1 sp_a sp_c sp_s2 sp_b : SurfPos} {ev_a ev_b : List Event} (ho : GLit '[' sp_br sp_o)
    (hq : GLit '?' sp_o sp_q) (hs1 : SSeparateLines n sp_q sp_s1) (ha : TFlowNode n .flowIn sp_s1 sp_a ev_a)
    (hc : GLit ':' sp_a sp_c) (hs2 : SSeparateLines n sp_c sp_s2) (hb : TFlowNode n .flowIn sp_s2 sp_b ev_b) :
    TFlowOpenStack n 1 #[true] (.value false) sp_br sp_b (([] ++ ev_a) ++ ev_b) :=
  (((TFlowOpenStack.seqBase sp_br sp_br sp_o sp_o sp_o .sep [] ho (.none sp_o) (.betweenEmpty sp_o)).receiveQuestion
      rfl (.inr ⟨rfl, rfl⟩) hq).receiveNodeColon (kj := false) (.inr rfl) (.inl hs1) ha (fun h => nomatch h)
      (.inr rfl) hc).receiveNode (fun _ h => nomatch h) (.inl hs2) hb (fun h => nomatch h)
-- `[:` and `[? :` — receiveColonSep / receiveColonQuestion, trace kept
example {sp_br sp_o sp_c : SurfPos} (ho : GLit '[' sp_br sp_o) (hc : GLit ':' sp_o sp_c) :
    TFlowOpenStack n 1 #[true] (.colon false) sp_br sp_c [] :=
  (TFlowOpenStack.seqBase sp_br sp_br sp_o sp_o sp_o .sep [] ho (.none sp_o) (.betweenEmpty sp_o)).receiveColonSep
    rfl (.inr ⟨rfl, rfl⟩) hc
example {sp_br sp_o sp_q sp_s sp_c : SurfPos} (ho : GLit '{' sp_br sp_o) (hq : GLit '?' sp_o sp_q)
    (hs : SSeparateLines n sp_q sp_s) (hc : GLit ':' sp_s sp_c) :
    TFlowOpenStack n 1 #[false] (.colon false) sp_br sp_c [] :=
  ((TFlowOpenStack.mapBase sp_br sp_br sp_o sp_o sp_o .sep [] ho (.none sp_o) (.betweenEmpty sp_o)).receiveQuestion
    rfl (.inr ⟨rfl, rfl⟩) hq).receiveColonQuestion rfl (.inl hs) hc
-- `[&a` then `]`-decided empty content — receivePropsEmpty; `[&a b` — receivePropsContent
example {sp_br sp_o sp_p : SurfPos} {ev_p : List Event} (ho : GLit '[' sp_br sp_o)
    (hp : TCNsProperties n .flowIn sp_o sp_p ev_p) :
    TFlowOpenStack n 1 #[true] (.value false) sp_br sp_p ([] ++ ev_p) :=
  (TFlowOpenStack.seqBase sp_br sp_br sp_o sp_o sp_o .sep [] ho (.none sp_o) (.betweenEmpty sp_o)).receivePropsEmpty
    (fun _ h => nomatch h) (.inr ⟨rfl, rfl⟩) hp
example {sp_br sp_o sp_p sp_s sp_b : SurfPos} {ev_p ev_b : List Event} (ho : GLit '[' sp_br sp_o)
    (hp : TCNsProperties n .flowIn sp_o sp_p ev_p) (hs : SSeparateLines n sp_p sp_s)
    (hb : TFlowContent n .flowIn sp_s sp_b ev_b) :
    TFlowOpenStack n 1 #[true] (.value false) sp_br sp_b ([] ++ (ev_p ++ ev_b)) :=
  (TFlowOpenStack.seqBase sp_br sp_br sp_o sp_o sp_o .sep [] ho (.none sp_o) (.betweenEmpty sp_o)).receivePropsContent
    (kj := false) (fun _ h => nomatch h) (.inr ⟨rfl, rfl⟩) hp hs hb (fun h => nomatch h)
-- `[&a : b` — receiveColonPropsSep; `{? &a : b` — receiveColonPropsQuestion
example {sp_br sp_o sp_p sp_g sp_c sp_s sp_b : SurfPos} {ev_p ev_b : List Event} (ho : GLit '[' sp_br sp_o)
    (hp : TCNsProperties n .flowIn sp_o sp_p ev_p) (hg : SSeparateLines n sp_p sp_g) (hc : GLit ':' sp_g sp_c)
    (hs : SSeparateLines n sp_c sp_s) (hb : TFlowNode n .flowIn sp_s sp_b ev_b) :
    TFlowOpenStack n 1 #[true] (.value false) sp_br sp_b (([] ++ ev_p) ++ ev_b) :=
  ((TFlowOpenStack.seqBase sp_br sp_br sp_o sp_o sp_o .sep [] ho (.none sp_o) (.betweenEmpty sp_o)).receiveColonPropsSep
      rfl (.inr ⟨rfl, rfl⟩) hp (.some _ _ hg) hc).receiveNode (fun _ h => nomatch h) (.inl hs) hb (fun h => nomatch h)
example {sp_br sp_o sp_q sp_s sp_p sp_g sp_c : SurfPos} {ev_p : List Event} (ho : GLit '{' sp_br sp_o)
    (hq : GLit '?' sp_o sp_q) (hs : SSeparateLines n sp_q sp_s) (hp : TCNsProperties n .flowIn sp_s sp_p ev_p)
    (hg : SSeparateLines n sp_p sp_g) (hc : GLit ':' sp_g sp_c) :
    TFlowOpenStack n 1 #[false] (.colon false) sp_br sp_c ([] ++ ev_p) :=
  ((TFlowOpenStack.mapBase sp_br sp_br sp_o sp_o sp_o .sep [] ho (.none sp_o) (.betweenEmpty sp_o)).receiveQuestion
    rfl (.inr ⟨rfl, rfl⟩) hq).receiveColonPropsQuestion rfl (.inl hs) hp (.some _ _ hg) hc
-- `[&x b : c` — receivePropsNodeColon (the run decorates the key)
example {sp_br sp_o sp_p sp_s sp_b sp_c : SurfPos} {ev_p ev_b : List Event} (ho : GLit '[' sp_br sp_o)
    (hp : TCNsProperties n .flowIn sp_o sp_p ev_p) (hs : SSeparateLines n sp_p sp_s)
    (hb : TFlowContent n .flowIn sp_s sp_b ev_b) (hc : GLit ':' sp_b sp_c) :
    TFlowOpenStack n 1 #[true] (.colon false) sp_br sp_c ([] ++ (ev_p ++ ev_b)) :=
  (TFlowOpenStack.seqBase sp_br sp_br sp_o sp_o sp_o .sep [] ho (.none sp_o) (.betweenEmpty sp_o)).receivePropsNodeColon
    (kj := false) (.inl rfl) (.inr ⟨rfl, rfl⟩) hp hs hb (fun h => nomatch h) (.inr rfl) hc
-- `[[a` — a nest receives; the parent's trace prefix rides
example {sp_br sp_o1 sp_o2 sp_a : SurfPos} {ev : List Event} (h1 : GLit '[' sp_br sp_o1) (h2 : GLit '[' sp_o1 sp_o2)
    (ha : TFlowNode n .flowIn sp_o2 sp_a ev) :
    TFlowOpenStack n 2 (#[true].push true) (.value false) sp_br sp_a (([] ++ []) ++ ev) :=
  (TFlowOpenStack.seqNest 1 #[true] .sep .sep sp_br sp_o1 sp_o1 sp_o2 sp_o2 sp_o2 [] []
    (.seqBase sp_br sp_br sp_o1 sp_o1 sp_o1 .sep [] h1 (.none sp_o1) (.betweenEmpty sp_o1))
    (fun _ h => nomatch h) (.inr ⟨rfl, rfl⟩) h2 (.none sp_o2) (.betweenEmpty sp_o2)).receiveNode (fun _ h => nomatch h) (.inr ⟨rfl, rfl⟩) ha (fun h => nomatch h)
end P105Examples

/-! ### Priority 106 — S3 slice (3) PR 2b-ii(α): `accum_step_flow_trace`'s indicator arms (item 468), before proof

    The flow-indicator dispatcher (`accum_step_flow`) emits one silent token per step; the T
    stack must ride unchanged (`ev' = ev`) through `[` `{` (base / nested open), `,` and `]` `}`.
    Its depth-≥1 case re-reads the frame through `InteriorGap`, whose PROPS arm folds a held
    property run into the frame at the indicator — the domain the (β) carrier must cover.  Rule 2
    here: at every indicator over the P105 rows (plus held-run indicator rows), (a) the trace is
    silent, by arm; (b) a run is held at the indicator, by arm (InteriorGap.props' reach);
    (c) the depth distribution. -/
namespace P106
open L4YAML.Proofs.Serialization.TokenEvents (goOut)
open L4YAML.Proofs.Serialization.SerializationWellFormed (Event)

structure Frame where
  isSeq : Bool
  openOff : Nat := 0                          -- the opener's offset (the span's cut point)
  toks : List (Positioned YamlToken) := []    -- reversed, opener inclusive
  propPending : Bool := false

structure Tally where
  rows : Nat := 0
  scanned : Nat := 0
  steps : Nat := 0
  arm : List (String × Nat) := []        -- indicator arm
  twinSteps : Nat := 0                   -- (v) conclusion twins read (one per indicator step)
  twinBad : List String := []            -- (v) `scanFiltered` of the cut-and-closed span ≠ the stack lemma's trace
  refBad : List String := []             -- (v) `refLex` refuses the span
  aliasOut : List String := []           -- (v) alias whose anchor sits outside the cut (semantic, not grammar)
  heldArm : List (String × Nat) := []    -- indicator arriving on a held run, by arm
  depth : List (String × Nat) := []      -- depth before the indicator (0 = base open)
  silentBad : List String := []
  refusedOwn : List String := []

def own : List String :=
  ["{&a}", "{&a, b: c}", "[!t]", "[&a !t, b]", "[[&a]]", "{a: &b}", "[&a, &b]", "{&a: &b}"]
def allRows : List String := (P105.allRows ++ own).eraseDups
def pendings : List (List String) := [[], ["!a!"], ["!b!", "!a!"]]

def tally (rows : List String) : Tally := Id.run do
  let mut t : Tally := {}
  for s in rows do
    t := { t with rows := t.rows + 1 }
    match scanFiltered s with
    | .error _ => if own.contains s then t := { t with refusedOwn := s :: t.refusedOwn }
    | .ok ts =>
      t := { t with scanned := t.scanned + 1 }
      let mut st : List Frame := []
      for tk in ts do
        let isProp : Bool := match tk.val with | .anchor _ | .tag .. => true | _ => false
        let arm? : Option String := match tk.val with
          | .flowSequenceStart => some (if st.isEmpty then "baseOpen/seq" else "nestOpen/seq")
          | .flowMappingStart => some (if st.isEmpty then "baseOpen/map" else "nestOpen/map")
          | .flowEntry => some "comma"
          | .flowSequenceEnd => some "close/seq"
          | .flowMappingEnd => some "close/map"
          | _ => none
        match arm? with
        | some a =>
          t := { t with steps := t.steps + 1, arm := P100.bump t.arm a,
                        depth := P100.bump t.depth s!"{st.length}" }
          -- (v) the §7 lemma's conclusion, executably (review, round 1): the frame the step lands on,
          -- cut from its opener through the indicator and closed standalone, reads the lemma's trace
          -- under `scanFiltered` and `refLex` — `comma`: the top frame at `.sep` (`holdCommaLead`);
          -- `nestOpen/*`: the parent with the child opened and closed empty (`seqNest`/`mapNest`, the
          -- parent's trace kept); `close/*` nested: the parent after `receiveNode` of the closed child;
          -- `close/*` base: the whole span (`closeBase`'s `TFlowContent`); `baseOpen/*`: the opened frame
          -- closed empty (`openSeqBase`/`openMapBase`, trace `[]`).
          let twinOn : Nat → List (Positioned YamlToken) → String → Tally → Tally :=
            fun openOff toks closers t' => Id.run do
              let sub := P105.rstrip (String.Pos.Raw.extract s ⟨openOff⟩ ⟨tk.pos.offset + 1⟩) ++ closers
              let ev := (goOut toks.reverse []).1
              let (ok, okRef) := P104.twin sub ev
              let mut t'' := { t' with twinSteps := t'.twinSteps + 1 }
              if !ok then
                if P104.aliasOutside sub then t'' := { t'' with aliasOut := s!"{repr s}@{tk.pos.offset} {a}" :: t''.aliasOut }
                else t'' := { t'' with twinBad := s!"{repr s}@{tk.pos.offset} {a} {repr sub}" :: t''.twinBad }
              if !okRef then t'' := { t'' with refBad := s!"{repr s}@{tk.pos.offset} {a} {repr sub}" :: t''.refBad }
              return t''
          let closerOf : Frame → String := fun f => if f.isSeq then "]" else "}"
          match st with
          | f :: r =>
            if f.propPending then t := { t with heldArm := P100.bump t.heldArm a }
            -- (a) silent on the frame that receives the indicator (the parent of a nested open)
            for pnd in pendings do
              let before := goOut f.toks.reverse pnd
              let after := goOut (tk :: f.toks).reverse pnd
              if before != after then
                t := { t with silentBad := s!"{repr s}@{tk.pos.offset} {a} p={pnd}" :: t.silentBad }
            match tk.val with
            | .flowSequenceStart => t := twinOn f.openOff (tk :: f.toks) ("]" ++ closerOf f) t
            | .flowMappingStart => t := twinOn f.openOff (tk :: f.toks) ("}" ++ closerOf f) t
            | .flowEntry => t := twinOn f.openOff (tk :: f.toks) (closerOf f) t
            | _ =>
              match r with
              | p :: _ => t := twinOn p.openOff (tk :: p.toks) (closerOf p) t   -- `p.toks` already holds the child's
              | [] => t := twinOn f.openOff (tk :: f.toks) "" t
          | [] =>
            t := twinOn tk.pos.offset [tk] (if tk.val == .flowSequenceStart then "]" else "}") t
        | none => pure ()
        -- the walk
        st := st.map (fun f => { f with toks := tk :: f.toks })
        match tk.val with
        | .flowSequenceStart | .flowMappingStart =>
          st := { isSeq := tk.val == .flowSequenceStart, openOff := tk.pos.offset, toks := [tk] } :: st
        | .flowSequenceEnd | .flowMappingEnd =>
          st := (match st with | _ :: r => r.map (fun f => { f with propPending := false }) | [] => [])
          -- the parent received the closed node: its held run (if any) decorated it
        | .flowEntry | .value | .key =>
          st := (match st with | f :: r => { f with propPending := false } :: r | [] => [])
        | .scalar .. | .alias _ =>
          st := (match st with | f :: r => { f with propPending := false } :: r | [] => [])
        | .anchor _ | .tag .. =>
          st := (match st with | f :: r => { f with propPending := true } :: r | [] => [])
        | _ => pure ()
        let _ := isProp
  return t
end P106

section P106Test
def testFlowStep (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 106: S3 slice (3) PR 2b-ii(α) — accum_step_flow_trace's indicator arms, before proof"
  let t := P106.tally P106.allRows
  checkM state s!"P106(i) {t.rows} rows, {t.scanned} scanned, {t.steps} indicator steps; arms {t.arm}; silent bad {t.silentBad.length}"
    (t.silentBad.isEmpty && t.rows == 701 && t.scanned == 547 && t.steps == 587 &&
      t.arm.mergeSort (fun a b => a.1 ≤ b.1) ==
        [("baseOpen/map", 78), ("baseOpen/seq", 122), ("close/map", 92), ("close/seq", 148), ("comma", 107),
         ("nestOpen/map", 14), ("nestOpen/seq", 26)]) s!"{t.silentBad.take 5} | {t.arm}"
  -- P2 REFUTED on the ceilings (comma 1–3 → 7, close 1–3 → 7): the P105 rows already carry more held
  -- runs than the own list names; pinned exactly — this is the (β) carrier's domain at this dispatcher
  checkM state s!"P106(ii) a run held at the indicator (InteriorGap.props' reach), by arm: {t.heldArm}"
    (t.heldArm.mergeSort (fun a b => a.1 ≤ b.1) ==
      [("close/map", 2), ("close/seq", 5), ("comma", 7), ("nestOpen/seq", 2)]) s!"{t.heldArm}"
  -- P3 REFUTED on the floor (depth 1 = 327/587 = 56 % < 60 %: the 200 depth-0 base opens were under-counted)
  checkM state s!"P106(iii) depth before the indicator: {t.depth}"
    (t.depth.mergeSort (fun a b => a.1 ≤ b.1) == [("0", 200), ("1", 327), ("2", 46), ("3", 11), ("4", 3)]) s!"{t.depth}"
  -- P4 REFUTED on one row: `{&a: &b}` — `:` is an anchor character, so `&a:` is the anchor `a:` and the
  -- mapping has two properties-only nodes and no `:` (P104 (iv')'s `*y:` gotcha again); pinned exactly
  checkM state s!"P106(iv) own rows refused by the scanner: exactly the anchor-colon row {t.refusedOwn}"
    (t.refusedOwn == ["{&a: &b}"]) ""
  -- (v) the §7 lemmas' conclusions on the scanned spans (review, round 1; P5 recorded first).  P5 REFUTED
  -- on the alias count (3 → 2): P105's third alias-outside cut (`[&x [*x]]`) was a receive step INSIDE the
  -- child; at the indicator steps the parent's cut carries its own anchor.  Pinned exactly: the two rows
  -- whose anchor sits before the base opener.  (The instrument's first run read 3 bad — its nested-close
  -- twin appended the child's tokens to a parent that already held them; fixed, recorded in item 468.)
  checkM state s!"P106(v) the stack lemma's conclusion twin at every indicator step: {t.twinSteps} read, {t.twinBad.length} bad under scanFiltered, {t.refBad.length} under refLex, alias-outside cuts {t.aliasOut.length}"
    (t.twinSteps == t.steps && t.twinBad.isEmpty && t.refBad.isEmpty &&
      t.aliasOut.mergeSort (fun a b => a ≤ b) ==
        [s!"{repr "&x [*x]"}@6 close/seq", s!"{repr "&x {a: *x}"}@9 close/map"])
    s!"{t.twinBad.take 5} | {t.refBad.take 5} | {t.aliasOut}"
end P106Test

section P106Examples
open L4YAML.Surface L4YAML.Proofs.Serialization.TraceOf L4YAML.Proofs.Serialization.TraceOf.FlowWalk
open L4YAML.Proofs.Serialization.SerializationWellFormed (Event)
open L4YAML.Proofs.StreamAccum (FrameTail)
variable {n : Nat}
/-! P106 (v): the §7 indicator steps, hand-built over abstract premises, one per lemma. -/
-- `[a,` — comma on a `.value` tail, glued
example {sp_br sp_o sp_a sp_c : SurfPos} {ev : List Event} (ho : GLit '[' sp_br sp_o)
    (ha : TFlowNode n .flowIn sp_o sp_a ev) (hc : GLit ',' sp_a sp_c) :
    TFlowOpenStack n 1 #[true] .sep sp_br sp_c ([] ++ ev) :=
  ((TFlowOpenStack.seqBase sp_br sp_br sp_o sp_o sp_o .sep [] ho (.none sp_o) (.betweenEmpty sp_o)).receiveNode
    (kj := false) (fun _ h => nomatch h) (.inr ⟨rfl, rfl⟩) ha (fun h => nomatch h)).comma
    (fun h => nomatch h) (.inr ⟨rfl, rfl⟩) hc
-- `{a: [` — a nested open after the `:`'s separation; `[[` glued (`.sep` is leadFree)
example {sp_br sp_o sp_a sp_c sp_b sp_o2 : SurfPos} {ev : List Event} (ho : GLit '{' sp_br sp_o)
    (ha : TFlowNode n .flowIn sp_o sp_a ev) (hc : GLit ':' sp_a sp_c) (hs : SSeparateLines n sp_c sp_b)
    (h2 : GLit '[' sp_b sp_o2) :
    TFlowOpenStack n 2 (#[false].push true) .sep sp_br sp_o2 (([] ++ ev) ++ []) :=
  ((TFlowOpenStack.mapBase sp_br sp_br sp_o sp_o sp_o .sep [] ho (.none sp_o) (.betweenEmpty sp_o)).receiveNodeColon
    (kj := false) (.inl rfl) (.inr ⟨rfl, rfl⟩) ha (fun h => nomatch h) (.inr rfl) hc).openNestSeq
    (fun _ h => nomatch h) (.inl hs) h2
example {sp_br sp_o1 sp_o2 : SurfPos} (h1 : GLit '[' sp_br sp_o1) (h2 : GLit '{' sp_o1 sp_o2) :
    TFlowOpenStack n 2 (#[true].push false) .sep sp_br sp_o2 ([] ++ []) :=
  (TFlowOpenStack.seqBase sp_br sp_br sp_o1 sp_o1 sp_o1 .sep [] h1 (.none sp_o1) (.betweenEmpty sp_o1)).openNestMap
    (fun _ h => nomatch h) (.inr ⟨rfl, rfl⟩) h2
-- `[[a]` — the nested close lands on the parent as `.value true`; `{a: {}}`'s inner close likewise
example {sp_br sp_o1 sp_o2 sp_a sp_c : SurfPos} {ev : List Event} (h1 : GLit '[' sp_br sp_o1) (h2 : GLit '[' sp_o1 sp_o2)
    (ha : TFlowNode n .flowIn sp_o2 sp_a ev) (hc : GLit ']' sp_a sp_c) :
    TFlowOpenStack n 1 #[true] (.value true) sp_br sp_c ([] ++ ([] ++ ev)) :=
  TFlowOpenStack.closeNestedSeq
    (TFlowOpenStack.seqBase sp_br sp_br sp_o1 sp_o1 sp_o1 .sep [] h1 (.none sp_o1) (.betweenEmpty sp_o1))
    (fun _ h => nomatch h) (.inr ⟨rfl, rfl⟩) h2 (.none sp_o2)
    (.midNode false sp_o2 sp_o2 sp_a [] ev (.init sp_o2) ha (fun h => nomatch h)) (.inr ⟨rfl, rfl⟩) hc
example {sp_br sp_o sp_a sp_c sp_b sp_o2 sp_e : SurfPos} {ev : List Event} (ho : GLit '{' sp_br sp_o)
    (ha : TFlowNode n .flowIn sp_o sp_a ev) (hc : GLit ':' sp_a sp_c) (hs : SSeparateLines n sp_c sp_b)
    (h2 : GLit '{' sp_b sp_o2) (he : GLit '}' sp_o2 sp_e) :
    TFlowOpenStack n 1 #[false] (.value true) sp_br sp_e (([] ++ ev) ++ []) :=
  TFlowOpenStack.closeNestedMap
    ((TFlowOpenStack.mapBase sp_br sp_br sp_o sp_o sp_o .sep [] ho (.none sp_o) (.betweenEmpty sp_o)).receiveNodeColon
      (kj := false) (.inl rfl) (.inr ⟨rfl, rfl⟩) ha (fun h => nomatch h) (.inr rfl) hc)
    (fun _ h => nomatch h) (.inl hs) h2 (.none sp_o2) (.betweenEmpty sp_o2) (.inr ⟨rfl, rfl⟩) he
-- `[a]` / `{}` — the base close hands the content out, the stack is `nil`
example {sp_br sp_o sp_a sp_c : SurfPos} {ev : List Event} (ho : GLit '[' sp_br sp_o)
    (ha : TFlowNode n .flowIn sp_o sp_a ev) (hc : GLit ']' sp_a sp_c) :
    TFlowContent n .flowOut sp_br sp_c ([] ++ ev) ∧ TFlowStackB n 0 #[] (.value true) sp_br sp_br [] :=
  TSeqFrame.closeBase (sp_block := sp_br) ho (.none sp_o) (.midNode false sp_o sp_o sp_a [] ev (.init sp_o) ha (fun h => nomatch h))
    (.inr ⟨rfl, rfl⟩) hc
example {sp_br sp_o sp_c : SurfPos} (ho : GLit '{' sp_br sp_o) (hc : GLit '}' sp_o sp_c) :
    TFlowContent n .flowOut sp_br sp_c [] ∧ TFlowStackB n 0 #[] (.value true) sp_br sp_br [] :=
  TMapFrame.closeBase (sp_block := sp_br) ho (.none sp_o) (.betweenEmpty sp_o) (.inr ⟨rfl, rfl⟩) hc
end P106Examples

/-! Priority 107 (item 469, PR 2b-ii α2): `FlowArm` — `accum_step_flow`'s arm witness — read off the
    scanner's OWN step before it is stated.  The arm is the projection `(sc.flowLevel, sc.flowStack.back?, c)`
    (Rule 8: no ghost choice); every field a constructor claims about the post-state — `s'.flowLevel`,
    `s'.flowStack`, `tailOf s'.tokens` — and every tail premise it takes from the pre-state is decided
    here at each indicator step over the P106 rows, stepping `scanNextToken` as `scanLoop` does. -/
namespace P107

structure Tally where
  rows : Nat := 0
  scanned : Nat := 0
  steps : Nat := 0
  arm : List (String × Nat) := []
  sizeBad : List String := []      -- `sc.flowStack.size ≠ sc.flowLevel` at an indicator
  kindBad : List String := []      -- a closer whose kind ≠ the top of `sc.flowStack`
  postBad : List String := []      -- `s'.flowLevel` / `s'.flowStack` / `tailOf s'.tokens` ≠ the arm's claim
  preBad : List String := []       -- `,` on a `.sep` tail / nested open on a `.value` tail
  multiBad : List String := []     -- a step that emitted more than one real token with an indicator
  heldArm : List (String × Nat) := []  -- a property run held at the indicator (`InteriorGap.props`), by arm
  refusedOwn : List String := []

/-- The arm as a projection of the pre-state and the indicator; `none` = not an indicator. -/
def armOf (sc : ScannerState) : YamlToken → Option String
  | .flowSequenceStart => some (if sc.flowLevel == 0 then "baseOpen/seq" else "nestOpen/seq")
  | .flowMappingStart => some (if sc.flowLevel == 0 then "baseOpen/map" else "nestOpen/map")
  | .flowEntry => some "comma"
  | .flowSequenceEnd => some (if sc.flowLevel == 1 then "closeBase/seq" else "closeNested/seq")
  | .flowMappingEnd => some (if sc.flowLevel == 1 then "closeBase/map" else "closeNested/map")
  | _ => none

/-- The `(pre, post)` states of every `scanNextToken` step, as `scan` runs them; `none` if refused. -/
def stepsOf (s : String) : Option (List (ScannerState × ScannerState)) := Id.run do
  let s0 := (ScannerState.mk' s).emit .streamStart
  let s0 := match s0.peek? with
    | some '\uFEFF' => s0.consumeBOM
    | _ => s0
  let mut sc := s0
  let mut acc : List (ScannerState × ScannerState) := []
  for _ in [0:(s.utf8ByteSize + 1) * 4] do
    match scanNextToken sc with
    | .error _ => return none
    | .ok none => return some acc.reverse
    | .ok (some s') => acc := (sc, s') :: acc; sc := s'
  return none

open L4YAML.Proofs.StreamAccum in
def tally (rows : List String) : Tally := Id.run do
  let mut t : Tally := {}
  for s in rows do
    t := { t with rows := t.rows + 1 }
    -- the acceptance oracle is `scanFiltered` (P1 REFUTED on the first run: `stepsOf` alone accepted the
    -- 11 rows `scanLoop` refuses at end of input — an unclosed flow — so it read 558/593, not 547/587)
    match scanFiltered s, stepsOf s with
    | .error _, _ | _, none => if P106.own.contains s then t := { t with refusedOwn := s :: t.refusedOwn }
    | .ok _, some sts =>
      t := { t with scanned := t.scanned + 1 }
      for (sc, s') in sts do
        let fresh := (s'.tokens.toList.drop sc.tokens.size).filter (fun p => p.val != .placeholder)
        let inds := fresh.filterMap fun p => (armOf sc p.val).map (·, p)
        match inds with
        | [] => pure ()
        | (a, p) :: rest =>
          let at_ := s!"{repr s}@{p.pos.offset} {a}"
          if !rest.isEmpty || fresh.length != 1 then t := { t with multiBad := at_ :: t.multiBad }
          t := { t with steps := t.steps + 1, arm := P100.bump t.arm a }
          if sc.flowStack.size != sc.flowLevel then t := { t with sizeBad := at_ :: t.sizeBad }
          let tl := tailOf sc.tokens
          let tl' := tailOf s'.tokens
          -- the tail the arm reads is the POST-gap tail `tl₂` of `accum_step_flow`'s `h_tuple`: a held
          -- property run is folded into the frame as an empty node first (`receivePropsEmpty`), so
          -- `[&a, b]`'s `,` sees `.value false`, not the opener's `.sep` (P3 REFUTED on the first run: 7 =
          -- exactly P106 (ii)'s held-run commas; the nested-open premise stays on `tl`, as `inject` has it)
          let held := !(trailingPropertyRun sc.tokens).isEmpty
          let tl₂ := if held then FrameTail.value false else tl
          if held then t := { t with heldArm := P100.bump t.heldArm a }
          let isSeq := p.val == .flowSequenceStart || p.val == .flowSequenceEnd
          let isOpen := p.val == .flowSequenceStart || p.val == .flowMappingStart
          let isClose := p.val == .flowSequenceEnd || p.val == .flowMappingEnd
          if isClose && sc.flowStack.back? != some isSeq then t := { t with kindBad := at_ :: t.kindBad }
          let postOk :=
            if isOpen then s'.flowLevel == sc.flowLevel + 1 && s'.flowStack == sc.flowStack.push isSeq && tl' == .sep
            else if isClose then s'.flowLevel + 1 == sc.flowLevel && s'.flowStack == sc.flowStack.pop && tl' == .value true
            else s'.flowLevel == sc.flowLevel && s'.flowStack == sc.flowStack && tl' == .sep
          if !postOk then
            t := { t with postBad := s!"{at_} tl'={repr tl'} fl {sc.flowLevel}→{s'.flowLevel}" :: t.postBad }
          let preOk :=
            if p.val == .flowEntry then tl₂ != .sep
            else if isOpen && sc.flowLevel > 0 then (match tl with | .value _ => false | _ => true)
            else true
          if !preOk then t := { t with preBad := s!"{at_} tl={repr tl}" :: t.preBad }
  return t

end P107

section P107Test
def testFlowArm (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 107: S3 slice (3) PR 2b-ii(α2) — FlowArm, accum_step_flow's arm witness, before statement"
  let t := P107.tally P106.allRows
  -- P1: the arms off the projection are P106's token-based arms, closes split base/nested as the opens
  checkM state s!"P107(i) {t.rows} rows, {t.scanned} scanned, {t.steps} indicator steps off the projection; arms {t.arm}; multi {t.multiBad.length}"
    (t.rows == 701 && t.scanned == 547 && t.steps == 587 && t.multiBad.isEmpty &&
      t.arm.mergeSort (fun a b => a.1 ≤ b.1) ==
        [("baseOpen/map", 78), ("baseOpen/seq", 122), ("closeBase/map", 78), ("closeBase/seq", 122),
         ("closeNested/map", 14), ("closeNested/seq", 26), ("comma", 107), ("nestOpen/map", 14), ("nestOpen/seq", 26)])
    s!"{t.arm} | {t.multiBad.take 5}"
  -- P4: the projection is coherent
  checkM state s!"P107(ii) flowStack.size = flowLevel {t.sizeBad.length} bad, closer kind = top of flowStack {t.kindBad.length} bad"
    (t.sizeBad.isEmpty && t.kindBad.isEmpty) s!"{t.sizeBad.take 5} | {t.kindBad.take 5}"
  -- P2: the post-state fields FlowArm's constructors claim
  checkM state s!"P107(iii) FlowArm's post-state fields (flowLevel, flowStack, tailOf s'.tokens) at every step: {t.postBad.length} bad"
    t.postBad.isEmpty s!"{t.postBad.take 8}"
  -- P3: the tail premises FlowArm's constructors take
  checkM state s!"P107(iv) FlowArm's tail premises (`,` never on .sep, nested open never on .value): {t.preBad.length} bad"
    t.preBad.isEmpty s!"{t.preBad.take 8}"
  -- P5
  checkM state s!"P107(v) own rows refused by the scanner: {t.refusedOwn}" (t.refusedOwn == ["{&a: &b}"]) ""
  -- P6 REFUTED twice: (a) six depth-0 opens carry a held run (`&a [b]`) — `accum_flow_open_depth0`'s
  -- `resume`/`propsContent` domain, which P106 (ii) (reading `InteriorGap.props` at depth ≥ 1) never
  -- counted; (b) P106's 5 held `close/seq` split 4 base + 1 nested.  The depth-≥1 rows still sum to 16.
  checkM state s!"P107(vi) a property run held at the indicator, by arm: {t.heldArm}"
    (t.heldArm.mergeSort (fun a b => a.1 ≤ b.1) ==
      [("baseOpen/map", 3), ("baseOpen/seq", 3), ("closeBase/map", 2), ("closeBase/seq", 4), ("closeNested/seq", 1),
       ("comma", 7), ("nestOpen/seq", 2)]) s!"{t.heldArm}"
end P107Test

def testLeafBridge (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Priority 100: S3 slice (1) — leaf span ↔ token payload (anchor / alias / tag), before proof"
  let t := P100.tally P100.allRows
  checkM state s!"P100(i) {t.rows} rows, {t.scanned} scanned, {t.leaves} leaf tokens: span events = tokenEvent on {t.ok}"
    (t.ok == t.leaves) s!"{repr (t.bad.take 8)}"
  for (s, tk, why) in t.bad.take 12 do
    checkM state s!"P100(i) mismatch {repr s} {tk}" false why
  for k in ["anchor", "alias", "verbatim", "secondary", "named", "primary"] do
    let n := P100.kindCount t k
    checkM state s!"P100(ii) kind {k}: {n} tokens" (n ≥ 3) ""
  -- (iii) the lexer's boolean anchor class is the scanner's loop condition, on every scalar value
  let m := P100.charMismatches
  checkM state s!"P100(iii) isAnchorCharBool = collectAnchorNameLoop's condition on every scalar value ({m} mismatches)" (m == 0) ""
  -- (iv) empty / singleton lexemes
  for s in ["&", "*", "& a", "!<>"] do
    checkM state s!"P100(iv) {repr s} is refused" (scanFiltered s).toOption.isNone ""
  checkM state "P100(iv) `!` scans to [useTag \"!\"]" ((P99.both "!").1 == some [.useTag "!"]) s!"{repr (P99.both "!").1}"
  checkM state "P100(iv) `!!` scans to [useTag \"!!\"]" ((P99.both "!!").1 == some [.useTag "!!"]) s!"{repr (P99.both "!!").1}"
  -- (v) the smallest term-level instances are the lemmas above; their scanner side:
  checkM state "P100(v) `&x` → [defineAnchor x]" ((P99.both "&x").1 == some [.defineAnchor "x"]) ""
  checkM state "P100(v) `*x` → scanner refuses an undefined alias (the trace side holds: traceOf_alias_x)" ((P99.both "*x").1 == none) ""
  -- (vi) the twins' full conclusions on positioned states: token array, landing state, trace of the consumed lexeme
  let (leaf, tag, disp) := P100.directRuns P100.allRows
  checkM state s!"P100(vi) scanAnchorOrAlias direct: {leaf.runs} runs, {leaf.ok} with the twin's token/landing/trace, {leaf.refused} refused"
    (leaf.ok == leaf.runs && leaf.refused == 0) s!"{repr (leaf.bad.take 6)}"
  checkM state s!"P100(vi) scanTag direct: {tag.runs} runs, {tag.ok} with the twin's token/landing/trace, {tag.refused} refused"
    (tag.ok == tag.runs && tag.refused == 0) s!"{repr (tag.bad.take 6)}"
  -- (vii) the content dispatcher's arms (the consumers `ScannerShape.dispatchContent_*_trace`): every accepted run satisfies
  checkM state s!"P100(vii) dispatchContent direct: {disp.runs} runs, {disp.ok} accepted with the conclusion, {disp.refused} refused by the arm's guards, {disp.bad.length} bad"
    (disp.bad.isEmpty && disp.ok + disp.refused == disp.runs && disp.runs == 182) s!"{repr (disp.bad.take 6)}"
  -- the reading pinned exactly: per kind, and the refused set
  let okA := P100.kindOf disp.okByKind "anchor"; let rA := P100.kindOf disp.refusedByKind "anchor"
  let okL := P100.kindOf disp.okByKind "alias"; let rL := P100.kindOf disp.refusedByKind "alias"
  let okT := disp.ok - okA - okL; let rT := disp.refused - rA - rL
  checkM state s!"P100(vii) by kind — anchor {okA}/{rA}, alias {okL}/{rL}, tag {okT}/{rT} (accepted/refused)"
    (okA == 63 && rA == 0 && okL == 9 && rL == 11 && okT == 99 && rT == 0) ""
  checkM state s!"P100(vii) the {disp.refused} refusals are exactly the pinned flow-context alias sites, all trailingContent"
    (disp.refusedAt.length == P100.dispRefusedSites.length && P100.dispRefusedSites.all (disp.refusedAt.contains ·)
      && disp.refusedAt.all (P100.dispRefusedSites.contains ·) && disp.badRefusal.isEmpty)
    s!"got {repr disp.refusedAt.reverse} bad {repr disp.badRefusal}"
  -- (viii) the loop helpers at fuel 0 / 1 / 2 / full, accumulators "" and "pre"
  let L := P100.loopRuns P100.allRows
  checkM state s!"P100(viii) loop helpers: {L.runs} runs (4 loops × 4 fuels × 2 accumulators per leaf), {L.ok} with the span/landing clauses"
    (L.ok == L.runs) s!"{repr (L.bad.take 8)}"

def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  test9g state
  test9h state
  test9cd state
  test9ab state
  test9e state
  test5_bound state
  test_filtered_prefix state
  testFlowParserHelpers state
  testHandleBlockMappingKeyEntryMono state
  testCloseStaleExplicitKey state
  testCleanedResolveAliases state
  testScalarFinishBridges state
  testAnchorIndex state
  testFrameLevelKinds state
  testPendingKeys state
  testDedentHook state
  testHookCarrier state
  testTokenCarrierWalk state
  testColFloorWalk state
  testColFloorHelpers state
  testRegisterWitnessWalk state
  testRegisterWitnessHelpers state
  testMaximalPropertyLeaves state
  testMaximalTagLeaves state
  testGluedFlowValue state
  testGluedScannerLemmas state
  testColZeroLanding state
  testNotQuestionPark state
  testMarkedColsDomain state
  testColZeroParks state
  testKslotDomain state
  testFlowCarrier state
  testKslotPay state
  testOwnMark state
  testCompactCover state
  testEntryChain state
  testCompactChain state
  testRefusedAtParks state
  testInlDeclinesPaid state
  testKslotEDomain state
  testColonChainRelay state
  testHeldChainRelay state
  testArmedOuterPartition state
  testArmedOuterLemma state
  testPackAltMarkTauto state
  testPackAltMarkTautoRegisters state
  testDedentMarksSurvive state
  testMarkFloorAndSeqTopKey state
  testNoMapLineArm state
  testThreeArmsFields state
  testSeqTopRefusedArm state
  testPackChainCarrier state
  testPackStrictGuardLane state
  testPackAltMarks state
  testPackAltNegative state
  testPackAltUnmarkedRefused state
  testPackBirthsOnDrop state

  testQuestionMarkColumn state
  testK1Lanes state
  testCloseFVCover state
  testFlowOpenRegister state
  testFlowCloseRegister state
  testContentRegister state
  testCloseColonOuter state
  testDirectiveLine state
  testDirectiveLoops state
  testExplicitColonRegister state
  testTraceOfLeafEvents state
  testTraceOfBlockLedger state
  testExplicitOnlyStream state
  testDirectiveAfterContent state
  testRootFrameBound state
  testRootFrameSupplyRead state
  testRootSiblingLedger state
  testSiblingDashFrames state
  testValueLineResume state
  testSeqTopKeyFace state
  testSeqTopKeyLemma state
  testSiblingArmDomain state
  testSeqTopResumeCtx state
  testOpenerSiblingAccepted state
  testOpenerSeqTopRefused state
  testCursorFace state
  testDeadRegisterIdentity state
  testCursorFaceScope state
  testLiveRegisterSeqTop state
  testRootSiblingLevel state
  testRootSiblingResumes state
  testNoPopAfterClosedNode state
  testDeeperLandingResidueArm state
  testDeeperLandingPaid state
  testNoPopDedentL1 state
  testFloorLevelInstances state
  testSeqTopNoPopFaces state
  testSeqTopLeDispatchWalk state
  testValueLandedSeq state
  testMapTopSibling state
  testMapTopLemmaWalk state
  testLandedNoPushHalf state
  testRootFrameSupply state
  testFlowParkFrames state
  testFlowFramesChain state
  testIndentSubsetLemmas state
  testLiveKeyTopInvariant state
  testInputAheadExports state
  testDeeperLandingOnMapPark state
  testParseOkCheckFrom state
  testParseNodeCF state
  testBlockScalarTailEof state
  testTokenEventExtractorsSeam state
  testTagHandleShape state
  testTokenStateOkRestatement state
  testAlignLemmas state
  testDirectivesClosedScan state
  testStreamEndLastScan state
  testStreamEndNoEvent state
  testGoAppendStreamEnd state
  testScanLoopStreamEndFuel state
  testStuckAtDocStart state
  testDocStartLive state
  testFlowSyncPrereqs state
  testLiveInvCarrier state
  testLoopDeadDischarge state
  testSetLemmas state
  testTagUsesShaped state
  testNoComment state
  testGammaBal state
  testGammaDepth state
  testTraceBridge state
  testLeafBridge state
  testDocBridge state
  testFlowBridge state
  testFlowWalk state
  testFlowAlgebra state
  testFlowReceive state
  testFlowStep state
  testFlowArm state
  let results ← finish state
  return { name := "adversarialinstantiation",
           label := "Adversarial Instantiation Tests (sorry audit)",
           sourceFile := "Tests/AdversarialInstantiation.lean",
           tests := results }

end Tests.AdversarialInstantiation

end Blanket
