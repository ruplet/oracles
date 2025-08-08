pandoc chapters/preface.md chapters/introduction.md -o thesis.pdf -f markdown --bibliography references.bib --citeproc --csl apa.csl

# pdflatex main.tex && biber main && pdflatex main.tex && pdflatex main.tex
