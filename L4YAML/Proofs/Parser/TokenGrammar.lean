module

public import L4YAML.Parser.TokenParser
public import L4YAML.Proofs.Serialization.SerializationWellFormed
public import L4YAML.Proofs.Serialization.TokenEvents

@[expose] public section

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Token grammar — the token image of the surface grammar

`TG ts s i j` is an inductive relation over index spans of a token array:
"tokens `[i, j)` derive the nonterminal `s`".  It is NOT defined by running
the parser; it mirrors the productions `parseStream`/`parseNode`/… follow
(`L4YAML/Parser/TokenParser.lean`) so that `parseStream_accepts`
(`StreamCompleteness.lean`) can be proved by induction on the derivation.

`TokenStateOk ts` is the stateful half: the per-document anchor/tag-handle
discipline, stated as `SerializationWellFormed` of the event trace the
tokens denote (`TokenEvents.tokenEvents`, the serialization layer's own
extractor), so §3.2.2.2 is read off the existing `Event`/`Env` vocabulary
rather than re-invented. -/

namespace L4YAML.Proofs.TokenGrammar

open L4YAML
open L4YAML.TokenParser
open L4YAML.Proofs.Serialization.SerializationWellFormed

abbrev Toks := Array (Positioned YamlToken)

/-- The token at `i`, or `none` past the end — the array form of `ParseState.peek?`. -/
def tok (ts : Toks) (i : Nat) : Option YamlToken := (ts[i]?).map Positioned.val

/-- Position of token `i`; the parser's `getD` default past the end. -/
def posAt (ts : Toks) (i : Nat) : YamlPos :=
  match ts[i]? with
  | some t => t.pos
  | none => { offset := 0, line := 0, col := 0 }

def lineAt (ts : Toks) (i : Nat) : Nat := (posAt ts i).line
def colAt (ts : Toks) (i : Nat) : Nat := (posAt ts i).col

def isDirective : Option YamlToken → Bool
  | some (.versionDirective ..) | some (.tagDirective ..) => true
  | _ => false

def isProp : Option YamlToken → Bool
  | some (.anchor _) | some (.tag ..) => true
  | _ => false

def isBlockStart : Option YamlToken → Bool
  | some .blockSequenceStart | some .blockMappingStart => true
  | _ => false

/-- Tokens before which `parseNodeContent` yields an empty node without consuming. -/
def emptyFollower : Option YamlToken → Bool
  | some .key | some .value | some .blockEnd | some .flowEntry
  | some .flowSequenceEnd | some .flowMappingEnd | some .documentStart
  | some .documentEnd | some .streamEnd | some (.versionDirective ..)
  | some (.tagDirective ..) | none => true
  | _ => false

/-- `parseNode`'s `isSeqEntry`: the token before the node is `-`. -/
def isSeqEntryAt (ts : Toks) (i : Nat) : Bool :=
  match i with
  | 0 => false
  | k + 1 => match tok ts k with | some .blockEntry => true | _ => false

/-- `validateNodeProps`: a property and a block-collection start never share a line. -/
def PropsLineOk (ts : Toks) (i m : Nat) : Prop :=
  i < m → isBlockStart (tok ts m) = true → lineAt ts (m - 1) ≠ lineAt ts m

/-- `parseBlockMappingEntryValue`: a property after `:` (at `m`) on another line
    must sit right of the key column. -/
def ValuePropOk (ts : Toks) (m keyCol k : Nat) : Prop :=
  lineAt ts k = lineAt ts m ∨ keyCol < colAt ts k

def ValuePropsOk (ts : Toks) (m keyCol : Nat) : Prop :=
  (isProp (tok ts (m + 1)) = true → ValuePropOk ts m keyCol (m + 1)) ∧
  (isProp (tok ts (m + 1)) = true → isProp (tok ts (m + 2)) = true →
    ValuePropOk ts m keyCol (m + 2))

/-- A block collection as mapping value may not start on the key's line. -/
def KeyLineOk (ts : Toks) (p : Nat) (keyHasContent : Bool) (keyLine : Nat) : Prop :=
  isBlockStart (tok ts p) = true → keyHasContent = true → lineAt ts p ≠ keyLine

/-- `prepareDocumentState`: no block collection on the `---` line. -/
def DocStartLineOk (ts : Toks) (d : Nat) : Prop :=
  isBlockStart (tok ts (d + 1)) = true → lineAt ts (d + 1) ≠ lineAt ts d

/-- `---` at `d` (ending at `e = d + 1`), or no `---` and NO directive run before it
(`i = d`: the run `[i, d)` is empty).  Spec [209] `l-directive-document`: a non-empty
directive run MUST be followed by `---`; narrowed to the spec for 7.7 `parse_iff_grammar`
(S5 slice 2 — the parser's leniency on a `---`-less run is no longer a `TG` shape). -/
def DocStart (ts : Toks) (i d e : Nat) : Prop :=
  (tok ts d = some .documentStart ∧ e = d + 1 ∧ DocStartLineOk ts d) ∨
  (tok ts d ≠ some .documentStart ∧ e = d ∧ i = d)

/-- Separator before a flow item: none for the first item, `,` afterwards. -/
def FlowSep (ts : Toks) (first : Bool) (i q : Nat) : Prop :=
  (first = true ∧ q = i) ∨ (first = false ∧ tok ts i = some .flowEntry ∧ q = i + 1)

/-- `handleBlockMappingKeyEntry`'s `keyHasContent`, read at the token after `?`. -/
def keyHasContentAt (ts : Toks) (p : Nat) : Bool :=
  match tok ts p with
  | some .value | some .blockEnd => false
  | _ => true

/-- Nonterminals, one per parser function (with the parameters it threads). -/
inductive Sym where
  | stream (st : StreamState)
  | document
  | directives
  | node
  | props
  | content (se : Bool)
  | seqEntries
  | blockSeq
  | blockMap
  | mapEntries
  | keyEntry
  | entryValue (keyHasContent : Bool) (keyLine keyCol : Nat)
  | flowSeq
  | flowSeqItems (first : Bool)
  | singlePair
  | flowMap
  | flowMapEntries (first : Bool)
  | flowMapValue

/-- `TG ts s i j`: tokens `[i, j)` of `ts` derive `s`. -/
inductive TG (ts : Toks) : Sym → Nat → Nat → Prop where
  -- stream (§9.2 [211]), mirroring `parseStreamLoop`
  | stream_end {st i} :
      (tok ts i = some .streamEnd ∨ tok ts i = none) → TG ts (.stream st) i i
  | stream_docEnd {st i j} :
      tok ts i = some .documentEnd →
      TG ts (.stream .afterDocumentEnd) (i + 1) j → TG ts (.stream st) i j
  | stream_doc {st i m j t} :
      tok ts i = some t → t ≠ .documentEnd → t ≠ .streamEnd →
      st.validNextToken t = true →
      TG ts .document i m → i < m → tok ts m ≠ some .documentEnd →
      TG ts (.stream .afterDocument) m j → TG ts (.stream st) i j
  | stream_docTerminated {st i m j t} :
      tok ts i = some t → t ≠ .documentEnd → t ≠ .streamEnd →
      st.validNextToken t = true →
      TG ts .document i m → tok ts m = some .documentEnd →
      TG ts (.stream .afterDocumentEnd) (m + 1) j → TG ts (.stream st) i j
  -- document (§9.1 [210]): directives, optional `---`, root node
  | document {i d e m} :
      TG ts .directives i d → DocStart ts i d e → TG ts .node e m → TG ts .document i m
  | directives_nil {i} : isDirective (tok ts i) = false → TG ts .directives i i
  | directives_cons {i j} :
      isDirective (tok ts i) = true → TG ts .directives (i + 1) j → TG ts .directives i j
  -- node (§7.5/§8.1): alias, or properties then content
  | node_alias {i n} : tok ts i = some (.alias n) → TG ts .node i (i + 1)
  | node {i m j} :
      TG ts .props i m → PropsLineOk ts i m →
      TG ts (.content (isSeqEntryAt ts i)) m j → TG ts .node i j
  -- properties (§6.9 [96]): at most one anchor and one tag, either order
  | props_none {i} : isProp (tok ts i) = false → TG ts .props i i
  | props_anchor {i n} :
      tok ts i = some (.anchor n) → isProp (tok ts (i + 1)) = false → TG ts .props i (i + 1)
  | props_tag {i h s} :
      tok ts i = some (.tag h s) → isProp (tok ts (i + 1)) = false → TG ts .props i (i + 1)
  | props_anchorTag {i n h s} :
      tok ts i = some (.anchor n) → tok ts (i + 1) = some (.tag h s) → TG ts .props i (i + 2)
  | props_tagAnchor {i h s n} :
      tok ts i = some (.tag h s) → tok ts (i + 1) = some (.anchor n) → TG ts .props i (i + 2)
  -- content, mirroring `parseNodeContent`
  | content_scalar {se i c s} :
      tok ts i = some (.scalar c s) → TG ts (.content se) i (i + 1)
  | content_blockSeq {se i j} : TG ts .blockSeq i j → TG ts (.content se) i j
  | content_blockMap {se i j} : TG ts .blockMap i j → TG ts (.content se) i j
  | content_seqEntryEmpty {i} : tok ts i = some .blockEntry → TG ts (.content true) i i
  | content_implicitSeq {i j} :
      tok ts i = some .blockEntry → TG ts .seqEntries i j → TG ts (.content false) i j
  | content_flowSeq {se i j} : TG ts .flowSeq i j → TG ts (.content se) i j
  | content_flowMap {se i j} : TG ts .flowMap i j → TG ts (.content se) i j
  | content_empty {se i} : emptyFollower (tok ts i) = true → TG ts (.content se) i i
  -- block sequence (§8.2.1 [183]/[184]); entries also serve the compact form [186]
  | blockSeq {i k} :
      tok ts i = some .blockSequenceStart → TG ts .seqEntries (i + 1) k →
      tok ts k = some .blockEnd → TG ts .blockSeq i (k + 1)
  | seqEntries_nil {i} : tok ts i ≠ some .blockEntry → TG ts .seqEntries i i
  | seqEntries_cons {i m j} :
      tok ts i = some .blockEntry → TG ts .node (i + 1) m →
      TG ts .seqEntries m j → TG ts .seqEntries i j
  -- block mapping (§8.2.2 [187]–[195])
  | blockMap {i k} :
      tok ts i = some .blockMappingStart → TG ts .mapEntries (i + 1) k →
      tok ts k = some .blockEnd → TG ts .blockMap i (k + 1)
  | mapEntries_nil {i} :
      tok ts i ≠ some .key → tok ts i ≠ some .value → TG ts .mapEntries i i
  | mapEntries_key {i m j} :
      tok ts i = some .key → TG ts .keyEntry i m →
      TG ts .mapEntries m j → TG ts .mapEntries i j
  | mapEntries_value {i m j} :
      tok ts i = some .value → TG ts .node (i + 1) m →
      TG ts .mapEntries m j → TG ts .mapEntries i j
  | keyEntry {i m j} :
      tok ts i = some .key → TG ts .node (i + 1) m →
      TG ts (.entryValue (keyHasContentAt ts (i + 1)) (lineAt ts i) (colAt ts i)) m j →
      TG ts .keyEntry i j
  | entryValue_value {khc kl kc m j} :
      tok ts m = some .value → ValuePropsOk ts m kc → KeyLineOk ts (m + 1) khc kl →
      TG ts .node (m + 1) j → TG ts (.entryValue khc kl kc) m j
  | entryValue_retro {khc kl kc m j} :
      tok ts m = some .key → tok ts (m + 1) = some .value →
      TG ts .node (m + 2) j → TG ts (.entryValue khc kl kc) m j
  | entryValue_none {khc kl kc m} :
      tok ts m ≠ some .value → ¬ (tok ts m = some .key ∧ tok ts (m + 1) = some .value) →
      TG ts (.entryValue khc kl kc) m m
  -- flow sequence (§7.4.1 [137]–[139], [150])
  | flowSeq {i k} :
      tok ts i = some .flowSequenceStart → TG ts (.flowSeqItems true) (i + 1) k →
      tok ts k = some .flowSequenceEnd → TG ts .flowSeq i (k + 1)
  | flowSeqItems_end {first i} :
      tok ts i = some .flowSequenceEnd → TG ts (.flowSeqItems first) i i
  | flowSeqItems_trailing {i} :
      tok ts i = some .flowEntry → tok ts (i + 1) = some .flowSequenceEnd →
      TG ts (.flowSeqItems false) i (i + 1)
  | flowSeqItems_pair {first i q m j} :
      tok ts i ≠ some .flowSequenceEnd → FlowSep ts first i q → tok ts q = some .key →
      TG ts .singlePair q m → TG ts (.flowSeqItems false) m j →
      TG ts (.flowSeqItems first) i j
  | flowSeqItems_node {first i q m j} :
      tok ts i ≠ some .flowSequenceEnd → FlowSep ts first i q →
      tok ts q ≠ some .key → tok ts q ≠ some .flowSequenceEnd →
      TG ts .node q m → TG ts (.flowSeqItems false) m j →
      TG ts (.flowSeqItems first) i j
  | singlePair_value {i r j} :
      tok ts i = some .key → TG ts .node (i + 1) r → tok ts r = some .value →
      TG ts .node (r + 1) j → TG ts .singlePair i j
  | singlePair_noValue {i r} :
      tok ts i = some .key → TG ts .node (i + 1) r → tok ts r ≠ some .value →
      TG ts .singlePair i r
  -- flow mapping (§7.4.2 [140]–[149])
  | flowMap {i k} :
      tok ts i = some .flowMappingStart → TG ts (.flowMapEntries true) (i + 1) k →
      tok ts k = some .flowMappingEnd → TG ts .flowMap i (k + 1)
  | flowMapEntries_end {first i} :
      tok ts i = some .flowMappingEnd → TG ts (.flowMapEntries first) i i
  | flowMapEntries_trailing {i} :
      tok ts i = some .flowEntry → tok ts (i + 1) = some .flowMappingEnd →
      TG ts (.flowMapEntries false) i (i + 1)
  | flowMapEntries_explicit {first i q r m j} :
      tok ts i ≠ some .flowMappingEnd → FlowSep ts first i q → tok ts q = some .key →
      TG ts .node (q + 1) r → TG ts .flowMapValue r m →
      TG ts (.flowMapEntries false) m j → TG ts (.flowMapEntries first) i j
  | flowMapEntries_implicit {first i q r m j} :
      tok ts i ≠ some .flowMappingEnd → FlowSep ts first i q →
      tok ts q ≠ some .key → tok ts q ≠ some .flowMappingEnd →
      TG ts .node q r → TG ts .flowMapValue r m →
      TG ts (.flowMapEntries false) m j → TG ts (.flowMapEntries first) i j
  | flowMapValue_value {r r' j} :
      (tok ts r = some .key ∧ r' = r + 1) ∨ (tok ts r ≠ some .key ∧ r' = r) →
      tok ts r' = some .value → TG ts .node (r' + 1) j → TG ts .flowMapValue r j
  | flowMapValue_none {r r'} :
      (tok ts r = some .key ∧ r' = r + 1) ∨ (tok ts r ≠ some .key ∧ r' = r) →
      tok ts r' ≠ some .value → TG ts .flowMapValue r r'

/-- The shape half: a well-formed token stream for `parseStream`. -/
def TokenGrammar (ts : Toks) : Prop :=
  tok ts 0 = some .streamStart ∧ ∃ j, TG ts (.stream .initial) 1 j ∧ j + 1 = ts.size

/-! ## State: the token array as an event trace -/

/-- The state half: every alias names an anchor committed earlier in its
    document, every tag handle is built in or `%TAG`-declared in its document —
    stated over the serialization layer's token trace `TokenEvents.tokenEvents`
    (EVENTSOF-CONCEPT §9 S2; S5 slice 2 retired the per-token twin that lived here,
    for 7.7 `parse_iff_grammar`).  Executable form: `checkFrom {} (tokenEvents ts)`
    via `serializationWellFormed_iff_check`. -/
def TokenStateOk (ts : Toks) : Prop :=
  SerializationWellFormed (L4YAML.Proofs.Serialization.TokenEvents.tokenEvents ts)

/-! ## Executable checker

`check ts fuel s i` is the recursive-descent reading of `TG`: it returns the
end of the span deriving `s` from `i`, or `none`.  `check_sound` makes it a
decision procedure for the Rule-2 probes. -/

def propsLineOk (ts : Toks) (i m : Nat) : Bool :=
  !(i < m) || !(isBlockStart (tok ts m)) || (lineAt ts (m - 1) != lineAt ts m)

def valuePropOk (ts : Toks) (m keyCol k : Nat) : Bool :=
  (lineAt ts k == lineAt ts m) || (keyCol < colAt ts k)

def valuePropsOk (ts : Toks) (m keyCol : Nat) : Bool :=
  (!(isProp (tok ts (m + 1))) || valuePropOk ts m keyCol (m + 1)) &&
  (!(isProp (tok ts (m + 1))) || !(isProp (tok ts (m + 2))) || valuePropOk ts m keyCol (m + 2))

def keyLineOk (ts : Toks) (p : Nat) (keyHasContent : Bool) (keyLine : Nat) : Bool :=
  !(isBlockStart (tok ts p)) || !keyHasContent || (lineAt ts p != keyLine)

def docStartLineOk (ts : Toks) (d : Nat) : Bool :=
  !(isBlockStart (tok ts (d + 1))) || (lineAt ts (d + 1) != lineAt ts d)

def isDocStart : Option YamlToken → Bool
  | some .documentStart => true
  | _ => false

def isDocEnd : Option YamlToken → Bool
  | some .documentEnd => true
  | _ => false

def isKey : Option YamlToken → Bool
  | some .key => true
  | _ => false

def isValue : Option YamlToken → Bool
  | some .value => true
  | _ => false

def isBlockEntry : Option YamlToken → Bool
  | some .blockEntry => true
  | _ => false

def isFlowSeqEnd : Option YamlToken → Bool
  | some .flowSequenceEnd => true
  | _ => false

def isFlowMapEnd : Option YamlToken → Bool
  | some .flowMappingEnd => true
  | _ => false

def isAnchor : Option YamlToken → Bool
  | some (.anchor _) => true
  | _ => false

def isTag : Option YamlToken → Bool
  | some (.tag ..) => true
  | _ => false

def flowSep (ts : Toks) (first : Bool) (i : Nat) : Option Nat :=
  if first then some i
  else if tok ts i = some .flowEntry then some (i + 1) else none

def check (ts : Toks) : Nat → Sym → Nat → Option Nat
  | 0, _, _ => none
  | f + 1, .stream st, i =>
    match tok ts i with
    | some .streamEnd => some i
    | none => some i
    | some .documentEnd => check ts f (.stream .afterDocumentEnd) (i + 1)
    | some t =>
      if st.validNextToken t then
        match check ts f .document i with
        | some m =>
          if i < m then
            if isDocEnd (tok ts m) then check ts f (.stream .afterDocumentEnd) (m + 1)
            else check ts f (.stream .afterDocument) m
          else none
        | none => none
      else none
  | f + 1, .document, i =>
    match check ts f .directives i with
    | some d =>
      if isDocStart (tok ts d) then
        if docStartLineOk ts d then check ts f .node (d + 1) else none
      else if d == i then check ts f .node d else none
    | none => none
  | f + 1, .directives, i =>
    if isDirective (tok ts i) then check ts f .directives (i + 1) else some i
  | f + 1, .node, i =>
    match tok ts i with
    | some (.alias _) => some (i + 1)
    | _ =>
      match check ts f .props i with
      | some m =>
        if propsLineOk ts i m then check ts f (.content (isSeqEntryAt ts i)) m else none
      | none => none
  | _ + 1, .props, i =>
    if isAnchor (tok ts i) then
      if isTag (tok ts (i + 1)) then some (i + 2)
      else if isProp (tok ts (i + 1)) then none else some (i + 1)
    else if isTag (tok ts i) then
      if isAnchor (tok ts (i + 1)) then some (i + 2)
      else if isProp (tok ts (i + 1)) then none else some (i + 1)
    else some i
  | f + 1, .content se, i =>
    match tok ts i with
    | some (.scalar ..) => some (i + 1)
    | some .blockSequenceStart => check ts f .blockSeq i
    | some .blockMappingStart => check ts f .blockMap i
    | some .blockEntry => if se then some i else check ts f .seqEntries i
    | some .flowSequenceStart => check ts f .flowSeq i
    | some .flowMappingStart => check ts f .flowMap i
    | t => if emptyFollower t then some i else none
  | f + 1, .blockSeq, i =>
    match tok ts i with
    | some .blockSequenceStart =>
      match check ts f .seqEntries (i + 1) with
      | some k => match tok ts k with | some .blockEnd => some (k + 1) | _ => none
      | none => none
    | _ => none
  | f + 1, .seqEntries, i =>
    if isBlockEntry (tok ts i) then
      match check ts f .node (i + 1) with
      | some m => check ts f .seqEntries m
      | none => none
    else some i
  | f + 1, .blockMap, i =>
    match tok ts i with
    | some .blockMappingStart =>
      match check ts f .mapEntries (i + 1) with
      | some k => match tok ts k with | some .blockEnd => some (k + 1) | _ => none
      | none => none
    | _ => none
  | f + 1, .mapEntries, i =>
    if isKey (tok ts i) then
      match check ts f .keyEntry i with
      | some m => check ts f .mapEntries m
      | none => none
    else if isValue (tok ts i) then
      match check ts f .node (i + 1) with
      | some m => check ts f .mapEntries m
      | none => none
    else some i
  | f + 1, .keyEntry, i =>
    match tok ts i with
    | some .key =>
      match check ts f .node (i + 1) with
      | some m =>
        check ts f (.entryValue (keyHasContentAt ts (i + 1)) (lineAt ts i) (colAt ts i)) m
      | none => none
    | _ => none
  | f + 1, .entryValue khc kl kc, i =>
    if isValue (tok ts i) then
      if valuePropsOk ts i kc && keyLineOk ts (i + 1) khc kl then check ts f .node (i + 1)
      else none
    else if isKey (tok ts i) && isValue (tok ts (i + 1)) then check ts f .node (i + 2)
    else some i
  | f + 1, .flowSeq, i =>
    match tok ts i with
    | some .flowSequenceStart =>
      match check ts f (.flowSeqItems true) (i + 1) with
      | some k => match tok ts k with | some .flowSequenceEnd => some (k + 1) | _ => none
      | none => none
    | _ => none
  | f + 1, .flowSeqItems first, i =>
    if isFlowSeqEnd (tok ts i) then some i
    else
      match flowSep ts first i with
      | none => none
      | some q =>
        if isKey (tok ts q) then
          match check ts f .singlePair q with
          | some m => check ts f (.flowSeqItems false) m
          | none => none
        else if isFlowSeqEnd (tok ts q) then (if first then none else some q)
        else
          match check ts f .node q with
          | some m => check ts f (.flowSeqItems false) m
          | none => none
  | f + 1, .singlePair, i =>
    match tok ts i with
    | some .key =>
      match check ts f .node (i + 1) with
      | some r => if isValue (tok ts r) then check ts f .node (r + 1) else some r
      | none => none
    | _ => none
  | f + 1, .flowMap, i =>
    match tok ts i with
    | some .flowMappingStart =>
      match check ts f (.flowMapEntries true) (i + 1) with
      | some k => match tok ts k with | some .flowMappingEnd => some (k + 1) | _ => none
      | none => none
    | _ => none
  | f + 1, .flowMapEntries first, i =>
    if isFlowMapEnd (tok ts i) then some i
    else
      match flowSep ts first i with
      | none => none
      | some q =>
        if isFlowMapEnd (tok ts q) then (if first then none else some q)
        else if isKey (tok ts q) then
          match check ts f .node (q + 1) with
          | some r =>
            match check ts f .flowMapValue r with
            | some m => check ts f (.flowMapEntries false) m
            | none => none
          | none => none
        else
          match check ts f .node q with
          | some r =>
            match check ts f .flowMapValue r with
            | some m => check ts f (.flowMapEntries false) m
            | none => none
          | none => none
  | f + 1, .flowMapValue, i =>
    if isKey (tok ts i) then
      if isValue (tok ts (i + 1)) then check ts f .node (i + 2) else some (i + 1)
    else if isValue (tok ts i) then check ts f .node (i + 1) else some i

/-- Shape check for a whole stream; fuel is generous (depth ≤ 4 per token). -/
def checkTokenGrammar (ts : Toks) : Bool :=
  match tok ts 0 with
  | some .streamStart =>
    match check ts (8 * ts.size + 8) (.stream .initial) 1 with
    | some j => j + 1 == ts.size
    | none => false
  | _ => false

/-! ### Soundness of the checker -/

lemma isDocStart_iff (o : Option YamlToken) : isDocStart o = true ↔ o = some .documentStart := by
  cases o with
  | none => simp [isDocStart]
  | some t => cases t <;> simp [isDocStart]

lemma isDocEnd_iff (o : Option YamlToken) : isDocEnd o = true ↔ o = some .documentEnd := by
  cases o with
  | none => simp [isDocEnd]
  | some t => cases t <;> simp [isDocEnd]

lemma isKey_iff (o : Option YamlToken) : isKey o = true ↔ o = some .key := by
  cases o with
  | none => simp [isKey]
  | some t => cases t <;> simp [isKey]

lemma isValue_iff (o : Option YamlToken) : isValue o = true ↔ o = some .value := by
  cases o with
  | none => simp [isValue]
  | some t => cases t <;> simp [isValue]

lemma isBlockEntry_iff (o : Option YamlToken) : isBlockEntry o = true ↔ o = some .blockEntry := by
  cases o with
  | none => simp [isBlockEntry]
  | some t => cases t <;> simp [isBlockEntry]

lemma isFlowSeqEnd_iff (o : Option YamlToken) :
    isFlowSeqEnd o = true ↔ o = some .flowSequenceEnd := by
  cases o with
  | none => simp [isFlowSeqEnd]
  | some t => cases t <;> simp [isFlowSeqEnd]

lemma isFlowMapEnd_iff (o : Option YamlToken) :
    isFlowMapEnd o = true ↔ o = some .flowMappingEnd := by
  cases o with
  | none => simp [isFlowMapEnd]
  | some t => cases t <;> simp [isFlowMapEnd]

lemma isAnchor_iff (o : Option YamlToken) : isAnchor o = true ↔ ∃ n, o = some (.anchor n) := by
  cases o with
  | none => simp [isAnchor]
  | some t => cases t <;> simp [isAnchor]

lemma isTag_iff (o : Option YamlToken) : isTag o = true ↔ ∃ h s, o = some (.tag h s) := by
  cases o with
  | none => simp [isTag]
  | some t => cases t <;> simp [isTag]

lemma isProp_eq_or (o : Option YamlToken) : isProp o = (isAnchor o || isTag o) := by
  cases o with
  | none => rfl
  | some t => cases t <;> rfl

lemma propsLineOk_sound {ts : Toks} {i m : Nat} (h : propsLineOk ts i m = true) :
    PropsLineOk ts i m := by
  intro hlt hb
  simp [propsLineOk, hlt, hb] at h
  exact h

lemma valuePropsOk_sound {ts : Toks} {m kc : Nat} (h : valuePropsOk ts m kc = true) :
    ValuePropsOk ts m kc := by
  unfold valuePropsOk at h
  rw [Bool.and_eq_true] at h
  refine ⟨fun h1 => ?_, fun h1 h2 => ?_⟩
  · have := h.1
    rw [h1] at this
    simpa [valuePropOk, ValuePropOk] using this
  · have := h.2
    rw [h1, h2] at this
    simpa [valuePropOk, ValuePropOk] using this

lemma keyLineOk_sound {ts : Toks} {p : Nat} {khc : Bool} {kl : Nat}
    (h : keyLineOk ts p khc kl = true) : KeyLineOk ts p khc kl := by
  intro hb hk
  simp [keyLineOk, hb, hk] at h
  exact h

lemma docStartLineOk_sound {ts : Toks} {d : Nat} (h : docStartLineOk ts d = true) :
    DocStartLineOk ts d := by
  intro hb
  simp [docStartLineOk, hb] at h
  exact h

lemma flowSep_sound {ts : Toks} {first : Bool} {i q : Nat} (h : flowSep ts first i = some q) :
    FlowSep ts first i q := by
  unfold flowSep at h
  split at h
  · cases h; exact Or.inl ⟨‹_›, rfl⟩
  · split at h
    · cases h; exact Or.inr ⟨by simp_all, ‹_›, rfl⟩
    · cases h

lemma check_sound (ts : Toks) : ∀ f s i j, check ts f s i = some j → TG ts s i j := by
  intro f
  induction f with
  | zero => intro s i j h; simp [check] at h
  | succ f ih =>
    intro s i j h
    cases s with
    | stream st =>
      simp only [check] at h
      split at h
      · cases h; exact .stream_end (.inl ‹_›)
      · cases h; exact .stream_end (.inr ‹_›)
      · exact .stream_docEnd ‹_› (ih _ _ _ h)
      · rename_i _ t hne hnd heq
        split at h
        · rename_i hvalid
          split at h
          · rename_i m hdoc
            split at h
            · rename_i hlt
              split at h
              · exact .stream_docTerminated heq hnd hne hvalid (ih _ _ _ hdoc)
                  ((isDocEnd_iff _).1 ‹_›) (ih _ _ _ h)
              · exact .stream_doc heq hnd hne hvalid (ih _ _ _ hdoc) hlt
                  (fun hc => ‹¬ isDocEnd (tok ts m) = true› ((isDocEnd_iff _).2 hc)) (ih _ _ _ h)
            · cases h
          · cases h
        · cases h
    | document =>
      simp only [check] at h
      split at h
      · rename_i d hdir
        split at h
        · rename_i hds
          split at h
          · exact .document (ih _ _ _ hdir)
              (Or.inl ⟨(isDocStart_iff _).1 hds, rfl, docStartLineOk_sound ‹_›⟩) (ih _ _ _ h)
          · cases h
        · split at h
          · exact .document (ih _ _ _ hdir)
              (Or.inr ⟨fun hc => ‹¬ isDocStart (tok ts d) = true› ((isDocStart_iff _).2 hc), rfl,
                (show i = d from (by simpa using (‹(d == i) = true›) : d = i).symm)⟩)
              (ih _ _ _ h)
          · cases h
      · cases h
    | directives =>
      simp only [check] at h
      split at h
      · exact .directives_cons ‹_› (ih _ _ _ h)
      · cases h; exact .directives_nil (by simp_all)
    | node =>
      simp only [check] at h
      split at h
      · cases h; exact .node_alias ‹_›
      · split at h
        · rename_i m hprops
          split at h
          · exact .node (ih _ _ _ hprops) (propsLineOk_sound ‹_›) (ih _ _ _ h)
          · cases h
        · cases h
    | props =>
      simp only [check] at h
      split at h
      · rename_i ha
        obtain ⟨n, hn⟩ := (isAnchor_iff _).1 ha
        split at h
        · rename_i ht
          obtain ⟨th, tsfx, ht'⟩ := (isTag_iff _).1 ht
          cases h; exact .props_anchorTag hn ht'
        · split at h
          · cases h
          · cases h; exact .props_anchor hn (by simp_all)
      · split at h
        · rename_i ht
          obtain ⟨th, tsfx, ht'⟩ := (isTag_iff _).1 ht
          split at h
          · rename_i ha
            obtain ⟨n, hn⟩ := (isAnchor_iff _).1 ha
            cases h; exact .props_tagAnchor ht' hn
          · split at h
            · cases h
            · cases h; exact .props_tag ht' (by simp_all)
        · cases h; exact .props_none (by rw [isProp_eq_or]; simp_all)
    | content se =>
      simp only [check] at h
      split at h
      · cases h; exact .content_scalar ‹_›
      · exact .content_blockSeq (ih _ _ _ h)
      · exact .content_blockMap (ih _ _ _ h)
      · rename_i hbe
        split at h
        · rename_i hse; cases h; rw [hse]; exact .content_seqEntryEmpty hbe
        · rename_i hse; rw [Bool.not_eq_true] at hse; rw [hse]
          exact .content_implicitSeq hbe (ih _ _ _ h)
      · exact .content_flowSeq (ih _ _ _ h)
      · exact .content_flowMap (ih _ _ _ h)
      · split at h
        · cases h; exact .content_empty ‹_›
        · cases h
    | blockSeq =>
      simp only [check] at h
      split at h
      · split at h
        · rename_i k hent
          split at h
          · cases h; exact .blockSeq ‹_› (ih _ _ _ hent) ‹_›
          · cases h
        · cases h
      · cases h
    | seqEntries =>
      simp only [check] at h
      split at h
      · split at h
        · exact .seqEntries_cons ((isBlockEntry_iff _).1 ‹_›) (ih _ _ _ ‹_›) (ih _ _ _ h)
        · cases h
      · cases h
        exact .seqEntries_nil (fun hc => ‹¬ isBlockEntry (tok ts i) = true› ((isBlockEntry_iff _).2 hc))
    | blockMap =>
      simp only [check] at h
      split at h
      · split at h
        · rename_i k hent
          split at h
          · cases h; exact .blockMap ‹_› (ih _ _ _ hent) ‹_›
          · cases h
        · cases h
      · cases h
    | mapEntries =>
      simp only [check] at h
      split at h
      · split at h
        · exact .mapEntries_key ((isKey_iff _).1 ‹_›) (ih _ _ _ ‹_›) (ih _ _ _ h)
        · cases h
      · split at h
        · split at h
          · exact .mapEntries_value ((isValue_iff _).1 ‹_›) (ih _ _ _ ‹_›) (ih _ _ _ h)
          · cases h
        · cases h
          exact .mapEntries_nil (fun hc => ‹¬ isKey (tok ts i) = true› ((isKey_iff _).2 hc))
            (fun hc => ‹¬ isValue (tok ts i) = true› ((isValue_iff _).2 hc))
    | keyEntry =>
      simp only [check] at h
      split at h
      · split at h
        · exact .keyEntry ‹_› (ih _ _ _ ‹_›) (ih _ _ _ h)
        · cases h
      · cases h
    | entryValue khc kl kc =>
      simp only [check] at h
      split at h
      · split at h
        · rename_i hok
          simp only [Bool.and_eq_true] at hok
          exact .entryValue_value ((isValue_iff _).1 ‹_›) (valuePropsOk_sound hok.1)
            (keyLineOk_sound hok.2) (ih _ _ _ h)
        · cases h
      · split at h
        · rename_i hkv
          simp only [Bool.and_eq_true, isKey_iff, isValue_iff] at hkv
          exact .entryValue_retro hkv.1 hkv.2 (ih _ _ _ h)
        · cases h
          exact .entryValue_none (fun hc => ‹¬ isValue (tok ts i) = true› ((isValue_iff _).2 hc))
            (fun hc => ‹¬ (isKey (tok ts i) && isValue (tok ts (i + 1))) = true›
              (by simp only [Bool.and_eq_true, isKey_iff, isValue_iff]; exact hc))
    | flowSeq =>
      simp only [check] at h
      split at h
      · split at h
        · rename_i k hitems
          split at h
          · cases h; exact .flowSeq ‹_› (ih _ _ _ hitems) ‹_›
          · cases h
        · cases h
      · cases h
    | flowSeqItems first =>
      simp only [check] at h
      split at h
      · cases h; exact .flowSeqItems_end ((isFlowSeqEnd_iff _).1 ‹_›)
      · rename_i hne
        have hne' : tok ts i ≠ some .flowSequenceEnd :=
          fun hc => hne ((isFlowSeqEnd_iff _).2 hc)
        split at h
        · cases h
        · rename_i q hsep
          have hsep' := flowSep_sound hsep
          split at h
          · split at h
            · exact .flowSeqItems_pair hne' hsep' ((isKey_iff _).1 ‹_›) (ih _ _ _ ‹_›) (ih _ _ _ h)
            · cases h
          · split at h
            · split at h
              · cases h
              · cases h
                rcases hsep' with ⟨hf, _⟩ | ⟨hf, hfe, hq⟩
                · simp_all
                · subst hf; subst hq
                  exact .flowSeqItems_trailing hfe ((isFlowSeqEnd_iff _).1 ‹_›)
            · split at h
              · exact .flowSeqItems_node hne' hsep'
                  (fun hc => ‹¬ isKey (tok ts q) = true› ((isKey_iff _).2 hc))
                  (fun hc => ‹¬ isFlowSeqEnd (tok ts q) = true› ((isFlowSeqEnd_iff _).2 hc))
                  (ih _ _ _ ‹_›) (ih _ _ _ h)
              · cases h
    | singlePair =>
      simp only [check] at h
      split at h
      · split at h
        · rename_i r hkey
          split at h
          · exact .singlePair_value ‹_› (ih _ _ _ hkey) ((isValue_iff _).1 ‹_›) (ih _ _ _ h)
          · cases h
            exact .singlePair_noValue ‹_› (ih _ _ _ hkey)
              (fun hc => ‹¬ isValue (tok ts j) = true› ((isValue_iff _).2 hc))
        · cases h
      · cases h
    | flowMap =>
      simp only [check] at h
      split at h
      · split at h
        · rename_i k hent
          split at h
          · cases h; exact .flowMap ‹_› (ih _ _ _ hent) ‹_›
          · cases h
        · cases h
      · cases h
    | flowMapEntries first =>
      simp only [check] at h
      split at h
      · cases h; exact .flowMapEntries_end ((isFlowMapEnd_iff _).1 ‹_›)
      · rename_i hne
        have hne' : tok ts i ≠ some .flowMappingEnd :=
          fun hc => hne ((isFlowMapEnd_iff _).2 hc)
        split at h
        · cases h
        · rename_i q hsep
          have hsep' := flowSep_sound hsep
          split at h
          · split at h
            · cases h
            · cases h
              rcases hsep' with ⟨hf, _⟩ | ⟨hf, hfe, hq⟩
              · simp_all
              · subst hf; subst hq
                exact .flowMapEntries_trailing hfe ((isFlowMapEnd_iff _).1 ‹_›)
          · split at h
            · split at h
              · split at h
                · exact .flowMapEntries_explicit hne' hsep' ((isKey_iff _).1 ‹_›)
                    (ih _ _ _ ‹_›) (ih _ _ _ ‹_›) (ih _ _ _ h)
                · cases h
              · cases h
            · split at h
              · split at h
                · exact .flowMapEntries_implicit hne' hsep'
                    (fun hc => ‹¬ isKey (tok ts q) = true› ((isKey_iff _).2 hc))
                    (fun hc => ‹¬ isFlowMapEnd (tok ts q) = true› ((isFlowMapEnd_iff _).2 hc))
                    (ih _ _ _ ‹_›) (ih _ _ _ ‹_›) (ih _ _ _ h)
                · cases h
              · cases h
    | flowMapValue =>
      simp only [check] at h
      split at h
      · rename_i hk
        have hk' := (isKey_iff _).1 hk
        split at h
        · exact .flowMapValue_value (Or.inl ⟨hk', rfl⟩) ((isValue_iff _).1 ‹_›) (ih _ _ _ h)
        · cases h
          exact .flowMapValue_none (Or.inl ⟨hk', rfl⟩)
            (fun hc => ‹¬ isValue (tok ts (i + 1)) = true› ((isValue_iff _).2 hc))
      · rename_i hk
        have hk' : tok ts i ≠ some .key := fun hc => hk ((isKey_iff _).2 hc)
        split at h
        · exact .flowMapValue_value (Or.inr ⟨hk', rfl⟩) ((isValue_iff _).1 ‹_›) (ih _ _ _ h)
        · cases h
          exact .flowMapValue_none (Or.inr ⟨hk', rfl⟩)
            (fun hc => ‹¬ isValue (tok ts i) = true› ((isValue_iff _).2 hc))

/-- `checkTokenGrammar` is a sound decision procedure for the shape half. -/
lemma checkTokenGrammar_sound {ts : Toks} (h : checkTokenGrammar ts = true) : TokenGrammar ts := by
  unfold checkTokenGrammar at h
  split at h
  · split at h
    · exact ⟨‹_›, _, check_sound ts _ _ _ _ ‹_›, by simpa using h⟩
    · cases h
  · cases h

end L4YAML.Proofs.TokenGrammar
