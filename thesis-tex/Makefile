# Makefile for building thesis.pdf with Pandoc

PANDOC       := pandoc
PDF          := thesis.pdf
CHAPTERS     := chapters/preface.md \
                chapters/introduction.md \
                chapters/descriptive-complexity.md \
                chapters/affine-types.md \
                chapters/approach-2-icc.md \
                chapters/appendix-c-category-theory.md

# Add any extra flags you want (e.g., --pdf-engine=xelatex)
PANDOC_FLAGS := -f markdown --citeproc

.PHONY: all clean latex

all: $(PDF)

$(PDF): $(CHAPTERS)
	$(PANDOC) $(PANDOC_FLAGS) $^ -o $@

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

