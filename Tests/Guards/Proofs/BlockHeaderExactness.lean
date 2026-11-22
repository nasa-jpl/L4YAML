module

public import L4YAML.Parser.Composition

public meta import L4YAML.Parser.Composition
public import L4YAML.Parser.IndexedComposition

public meta import L4YAML.Parser.IndexedComposition
public import L4YAML.Scanner.Scalar

public meta import L4YAML.Scanner.Scalar
public import L4YAML.Scanner.IndexedScanner

public meta import L4YAML.Scanner.IndexedScanner
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # `[162] c-b-block-header` exactness (Rule 2 probes)

YAML 1.2.2 `[162]` is `([163] [164] | [164] [163]) s-b-comment`: at most one
chomping indicator (`-`/`+`) and at most one indentation indicator (`1`–`9`), in
either order.  Before this guard, `parseBlockHeaderLoop` consumed ANY two header
characters, so `|++`, `|--`, `|-+`, `|11`, `|1+`, `|+1`, `>-2`, `>2-` were all
accepted (`lake exe tryparse`, exit 0) while `|0`, `|1 1`, `|10`, `|+++`, `|2+-`
were refused.  `peekBlockHeaderIndicator?` now hides a repeated kind, so the
second indicator is left for the header-end check to refuse; the surface
production `SCBBlockHeader` is the spec shape and `parseBlockHeaderLoop_prod`
derives it.  Each probe runs BOTH pipelines, which must agree. -/

namespace L4YAML.Tests.Guards.BlockHeaderExactness

open L4YAML L4YAML.TokenParser L4YAML.TokenParser.Indexed

/-- Both pipelines accept the block scalar opened by `hdr`, with the same value. -/
def accepts (hdr : String) : Bool :=
  let src := hdr ++ "\n  x\n"
  match parseYamlSingle src, parseYamlSingleIx src with
  | .ok a, .ok b => a == b
  | _, _ => false

/-- Both pipelines refuse the block scalar opened by `hdr`, with the same error. -/
def refuses (hdr : String) : Bool :=
  let src := hdr ++ "\n  x\n"
  match parseYamlSingle src, parseYamlSingleIx src with
  | .error e₁, .error e₂ => e₁ == e₂
  | _, _ => false

/-! ## §1  The spec's header language: 0, 1 or 2 indicators, one of each kind -/

#guard accepts "|"
#guard accepts "|-"
#guard accepts "|+"
#guard accepts "|2"
#guard accepts ">"
#guard accepts "|1+"
#guard accepts "|+1"
#guard accepts ">-2"
#guard accepts ">2-"
#guard accepts "|+ # c"
#guard accepts "|2 # c"
#guard accepts "|- "

/-! ## §2  Refused: a repeated kind (the former over-acceptance), digit `0`, junk -/

#guard refuses "|++"
#guard refuses "|--"
#guard refuses "|-+"
#guard refuses "|+-"
#guard refuses "|11"
#guard refuses "|12"
#guard refuses ">2-2"
#guard refuses "|0"
#guard refuses "|10"
#guard refuses "|1 1"
#guard refuses "|+++"
#guard refuses "|2+-"
#guard refuses "|-2-"
#guard refuses "|+#c"
#guard refuses "|a"
#guard refuses "|+a"

/-- `parseBlockHeaderLoop` from `.clip`/`none` on `hdr` with `fuel`, both pipelines, as
    `(chomp, offset, column)`; `none` when the two pipelines disagree. -/
def loop? (hdr : String) (fuel : Nat) : Option (ChompStyle × Option Nat × Nat) :=
  let (ch, off, sc) := Scanner.parseBlockHeaderLoop (Scanner.ScannerState.mk' hdr) .clip none fuel
  let (chx, offx, cx) :=
    Scanner.Indexed.parseBlockHeaderLoopIx (Indexed.IxCursor.start hdr) .clip none fuel
  if ch == chx && off == offx && sc.col == cx.pos.col then some (ch, off, sc.col) else none

-- Fuel 0 consumes nothing (the `_prod*` base cases).
#guard loop? "2-" 0 == some (ChompStyle.clip, none, 0)
#guard loop? "++" 0 == some (ChompStyle.clip, none, 0)
-- Fuel 1 takes exactly one indicator, of either kind.
#guard loop? "2-" 1 == some (ChompStyle.clip, some 2, 1)
#guard loop? "-2" 1 == some (ChompStyle.strip, none, 1)
#guard loop? "+" 1 == some (ChompStyle.keep, none, 1)
-- Fuel 2 (the scanner's budget) takes one of each, in either order.
#guard loop? "2-" 2 == some (ChompStyle.strip, some 2, 2)
#guard loop? "-2" 2 == some (ChompStyle.strip, some 2, 2)
#guard loop? "+9" 2 == some (ChompStyle.keep, some 9, 2)
-- A repeated kind is hidden at any fuel: the second indicator stays at the cursor.
#guard loop? "++" 2 == some (ChompStyle.keep, none, 1)
#guard loop? "--" 3 == some (ChompStyle.strip, none, 1)
#guard loop? "-+" 2 == some (ChompStyle.strip, none, 1)
#guard loop? "11" 2 == some (ChompStyle.clip, some 1, 1)
#guard loop? "2-2" 3 == some (ChompStyle.strip, some 2, 2)
-- `0` is not `[163]`; a non-indicator stops the loop.
#guard loop? "0" 2 == some (ChompStyle.clip, none, 0)
#guard loop? "" 2 == some (ChompStyle.clip, none, 0)
#guard loop? " #" 2 == some (ChompStyle.clip, none, 0)
-- `parseBlockHeaderLoop_saturated`: both kinds already read, nothing is consumed at any fuel.
#guard (Scanner.parseBlockHeaderLoop (Scanner.ScannerState.mk' "+3") .strip (some 1) 5).2.2.col == 0
#guard (Scanner.Indexed.parseBlockHeaderLoopIx (Indexed.IxCursor.start "+3") .keep (some 1) 5).2.2.pos.col
  == 0

end L4YAML.Tests.Guards.BlockHeaderExactness

end Blanket
