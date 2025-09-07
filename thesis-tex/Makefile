# Makefile for building thesis.pdf with Pandoc

PANDOC       := pandoc
PDF          := thesis.pdf
CHAPTERS     := chapters/introduction.md \
				chapters/unexplored.md \
                chapters/icc-introduction.md \
				chapters/icc-linear-logic.md \
				chapters/icc-recursion-theory.md \
				chapters/bounded-arithmetic.md \
				chapters/end-remarks.md

# Add any extra flags you want (e.g., --pdf-engine=xelatex)
PANDOC_FLAGS := -f markdown --citeproc

.PHONY: all clean latex

all: $(PDF)

$(PDF): $(CHAPTERS)
	$(PANDOC) $(PANDOC_FLAGS) preface.md $^ -o $@

clean:
	rm -f $(PDF)

# Optional: LaTeX toolchain build (if you keep the TeX route around)
latex:
	pdflatex main.tex
	biber main
	pdflatex main.tex
	pdflatex main.tex


# # About these files:
# - book.md: Pandoc-style Markdown file, containing all the theory behind the
# project.

# ## Pandoc command
# pandoc -o output.md book.md -f markdown -t gfm --bibliography references.bib --filter pandoc-citeproc --csl apa.csl

# ## Citation style
# apa
# source:
# https://github.com/citation-style-language/styles/blob/master/apa.csl

