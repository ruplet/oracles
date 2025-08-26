pandoc chapters/preface.md chapters/introduction.md chapters/descriptive-complexity.md chapters/affine-types.md chapters/appendix-c-category-theory.md -o thesis.pdf -f markdown --bibliography references.bib --citeproc --csl ieee.csl

# pdflatex main.tex && biber main && pdflatex main.tex && pdflatex main.tex
