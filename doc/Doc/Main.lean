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
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraFilesHtml := [
    ("Doc/L4YAML/graphs", "Verification/Key-Theorems/graphs"),
    ("Doc/L4YAML/graphs", "Verification/What-L4YAML-Proves/graphs")
  ]

def main (args : List String) := manualMain (%doc Doc.L4YAML) (options := args) (config := config)
