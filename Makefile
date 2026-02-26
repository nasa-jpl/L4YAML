doc:
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