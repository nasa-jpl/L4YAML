pdf:
	pandoc --pdf-engine=xelatex \
       --from markdown+lists_without_preceding_blankline+hard_line_breaks-implicit_figures \
       -H header.tex \
       --lua-filter=emoji-replace.lua \
       -V geometry:margin=1in \
       -V colorlinks=true \
       -V linkcolor=blue \
       -V urlcolor=blue \
       -V toccolor=blue \
       -V mainfont="DejaVu Sans" \
       -V monofont="DejaVu Sans Mono" \
       -V fontsize=11pt README.md -o README.pdf

api_doc:
	lake build DocGen4
	lake build Lean4Yaml:docs

import_graph:
	lake build graph
	lake exe graph --to Lean4Yaml docs/import_graph.dot
	dot -Tsvg docs/import_graph.dot -o docs/import_graph.svg
