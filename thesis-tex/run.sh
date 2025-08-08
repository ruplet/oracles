pandoc chapters/preface.md chapters/introduction.md chapters/descriptive-complexity.md chapters/curry-howard.md -o thesis.pdf -f markdown --bibliography references.bib --citeproc --csl apa.csl

# pdflatex main.tex && biber main && pdflatex main.tex && pdflatex main.tex
