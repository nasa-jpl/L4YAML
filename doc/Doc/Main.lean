/-
  L4YAML Documentation — Build entry point

  Build with:  lake exe l4yaml-doc
  Serve with:  python3 -m http.server 8000 --directory Doc/_out
-/
import VersoManual
import Doc.L4YAML

open Verso Doc
open Verso.Genre Manual

def config : RenderConfig where
  emitTeX := false
  -- Also emit the self-contained single page; the PDF is rendered from it so the
  -- document (and its bookmark outline) come out in true document order, instead of
  -- the alphabetical, lossy merge a multi-page directory would produce.
  emitHtmlSingle := .immediately
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraFilesHtml := [
    ("Doc/L4YAML/graphs", "Verification/Key-Theorems/graphs"),
    ("Doc/L4YAML/graphs", "Verification/What-L4YAML-Proves/graphs"),
    ("Doc/L4YAML/graphs", "Architecture/Import-Graph/graphs")
  ]

def main (args : List String) := manualMain (%doc Doc.L4YAML) (options := args) (config := config)
