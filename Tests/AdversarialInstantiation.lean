module

public import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch
public import L4YAML.Output.Emitter
public import L4YAML.Parser.Composition
public import L4YAML.Parser.IndexedComposition
public import L4YAML.Proofs.Parser.ParserGrammableBase
public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Proofs.Scanner.RegisterWitness
public import L4YAML.Proofs.Scanner.FlowAdjacency
public import L4YAML.Proofs.Scanner.FlowAdjacencyIx
public import L4YAML.Proofs.Serialization.TraceOf.Leaves
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
      ("%TAG !e!", "tag", 1, 0, 0), ("%TAG", "tag", 1, 0, 0), ("%TAG\n", "tag", 1, 0, 0),
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
  let partRows : List (String × Option (String × String)) :=
    [ ("%TAG !e!x", some ("!e!x", "")), ("%TAG !e! x", some ("!e!", "x")),
      ("%TAG !e!x!", some ("!e!x!", "")), ("%TAG ! !", some ("!", "!")),
      ("%TAG !a!!b! c", some ("!a!!b!", "c")), ("%TAG !e!%20", some ("!e!", "%20")),
      -- the reviewer's shape: the handle run is MAXIMAL, so `!e!x` is the handle and `y` the prefix
      -- (first written as refused; REFUTED by the run — the scanner accepts it)
      ("%TAG !e!x y", some ("!e!x", "y")), ("%TAG !e!\tx\n", some ("!e!", "x")),
      ("%TAG", some ("", "")), ("%TAG x", some ("x", "")),
      -- `[` is a `[39] ns-uri-char`: a prefix, not trailing content (first written as refused; REFUTED)
      ("%TAG !e! [", some ("!e!", "[")),
      ("%TAG !e!,x", some ("!e!", ",x")), ("%TAG !e!!x! y", some ("!e!!x!", "y")) ]
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
  testBlockScalarTailEof state
  let results ← finish state
  return { name := "adversarialinstantiation",
           label := "Adversarial Instantiation Tests (sorry audit)",
           sourceFile := "Tests/AdversarialInstantiation.lean",
           tests := results }

end Tests.AdversarialInstantiation

end Blanket
