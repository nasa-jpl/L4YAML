import L4YAML.Output.Events

/-!
# Reflection — INHABITATION / BOUNDARY probe for the escaped-trailing-tab fix (matrix defect B2)

Matrix defect **B2** (100%-matrix campaign, 2026-07; DE56/00–03): a double-quoted scalar whose
line ends in an **escaped** white character (`"…\t"` before a fold) lost that character, because the
line-fold trim (`trimTrailingWS`) stripped the decoded tab as if it were layout `s-white`.  By fold
time the escaped/literal distinction is gone — both are a bare `'\t'` in the accumulated content.

Per YAML 1.2.2 §7.3.1 an escaped tab (`ns-esc-tab` [62], written `\t` *or* `\<TAB>`) is an
`ns-double-char` (content), whereas a bare trailing tab is `s-white` layout that a fold [74]
`s-flow-folded` legitimately drops.  The fix threads a `protectedLen` boundary through
`collectDoubleQuotedLoop` marking the last `ns-double-char`; the fold trims only the *unescaped*
white run past it (`L4YAML/Parser/TokenParser.lean` → `Scanner/Scalar.lean`).

This is a [[feedback-inhabitation-debt-validate-target-defs]] probe: the `protectedLen` plumbing
*type-checks* under any bookkeeping, so the four escaped inputs it must FIX and the two literal-tab
inputs it must NOT disturb are pinned here by their full emitted event streams, where the fold is
actually performed.  Because the pipeline runs through `scanFiltered`/`parseStream` (`partial def`),
every check is `native_decide`.

The six inputs (`\` = backslash byte `0x5C`, `⇥` = literal TAB `0x09`, `·` = trailing space):
  * 00  `"1 trailing\t⏎    tab"`      escaped `\t`,   no trailing space  → keep tab
  * 01  `"2 trailing\t··⏎    tab"`    escaped `\t`,   two spaces         → keep tab, drop spaces
  * 02  `"3 trailing\⇥⏎    tab"`      escaped `\⇥`,   no trailing space  → keep tab
  * 03  `"4 trailing\⇥··⏎    tab"`    escaped `\⇥`,   two spaces         → keep tab, drop spaces
  * 04  `"5 trailing⇥⏎    tab"`       LITERAL `⇥`,    layout             → drop tab (boundary)
  * 05  `"6 trailing⇥··⏎    tab"`     LITERAL `⇥`,    layout             → drop tab (boundary)
-/

namespace EscapedTrailingTab

open L4YAML.Events

/-- The full event stream `streamToEvents` emits for `input`, or a fixed error marker. -/
private def run (input : String) : String :=
  match streamToEvents input with | .ok s => s | .error _ => "«parse-error»"

/-! ## Rule 5 (positive) — the four inputs B2 fixes, grounded on real bytes

An escaped trailing white char is content: the tab survives the fold and the line break folds to a
single space, so the value is `…<TAB> tab` (event format re-escapes the tab as `\t`). -/

/-- `data/DE56/00/in.yaml` — `\t` escape, no trailing layout space. -/
def inDE56_00 : String := "\"1 trailing\\t\n    tab\"\n"
def outDE56_00 : String := "+STR\n+DOC\n=VAL \"1 trailing\\t tab\n-DOC\n-STR\n"
theorem de56_00_keeps_escaped_tab : run inDE56_00 = outDE56_00 := by native_decide

/-- `data/DE56/01/in.yaml` — `\t` escape followed by two *unescaped* trailing spaces (dropped). -/
def inDE56_01 : String := "\"2 trailing\\t  \n    tab\"\n"
def outDE56_01 : String := "+STR\n+DOC\n=VAL \"2 trailing\\t tab\n-DOC\n-STR\n"
theorem de56_01_keeps_escaped_tab_drops_spaces : run inDE56_01 = outDE56_01 := by native_decide

/-- `data/DE56/02/in.yaml` — `\<TAB>` escape (backslash + literal tab), no trailing space. -/
def inDE56_02 : String := "\"3 trailing\\\t\n    tab\"\n"
def outDE56_02 : String := "+STR\n+DOC\n=VAL \"3 trailing\\t tab\n-DOC\n-STR\n"
theorem de56_02_keeps_escaped_literal_tab : run inDE56_02 = outDE56_02 := by native_decide

/-- `data/DE56/03/in.yaml` — `\<TAB>` escape followed by two trailing spaces (dropped). -/
def inDE56_03 : String := "\"4 trailing\\\t  \n    tab\"\n"
def outDE56_03 : String := "+STR\n+DOC\n=VAL \"4 trailing\\t tab\n-DOC\n-STR\n"
theorem de56_03_keeps_escaped_literal_tab_drops_spaces : run inDE56_03 = outDE56_03 := by native_decide

/-! ## Rule 2 (boundary) — the two inputs a naive "keep every trailing tab" would BREAK

Here the trailing tab is a bare literal (`s-white`, no backslash): it is layout and the fold must
still drop it, folding the line break to one space → value `…trailing tab`.  The pins carry NO `\t`
between `trailing` and ` tab`, so a regression to "keep the tab" is caught. -/

/-- `data/DE56/04/in.yaml` — a bare literal trailing tab is layout and is trimmed. -/
def inDE56_04 : String := "\"5 trailing\t\n    tab\"\n"
def outDE56_04 : String := "+STR\n+DOC\n=VAL \"5 trailing tab\n-DOC\n-STR\n"
theorem de56_04_drops_literal_tab : run inDE56_04 = outDE56_04 := by native_decide

/-- `data/DE56/05/in.yaml` — a bare literal trailing tab + spaces, all layout, all trimmed. -/
def inDE56_05 : String := "\"6 trailing\t  \n    tab\"\n"
def outDE56_05 : String := "+STR\n+DOC\n=VAL \"6 trailing tab\n-DOC\n-STR\n"
theorem de56_05_drops_literal_tab_and_spaces : run inDE56_05 = outDE56_05 := by native_decide

-- Axiom audit — the pins run the real parse pipeline (`Except`-monad + `parseStreamMarkedLoop`,
-- hence `Classical.choice`/`Quot.sound`), closed by `native_decide`.  No `sorryAx`.
/-- info: 'EscapedTrailingTab.de56_00_keeps_escaped_tab' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 de56_00_keeps_escaped_tab._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms de56_00_keeps_escaped_tab

end EscapedTrailingTab
