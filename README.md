# Oracle-oriented programming: a proof of concept

Current todo:
- present the history of the problem
- list all the papers I've read, including BibTeX references and mirrors

fajna konferencja
https://popl20.sigplan.org/track/POPL-2020-tutorialfest#program




# About these files:
- book.md: Pandoc-style Markdown file, containing all the theory behind the
project.

## Pandoc command
pandoc -o output.md book.md -f markdown -t gfm --bibliography references.bib --filter pandoc-citeproc --csl apa.csl

## Citation style
apa
source:
https://github.com/citation-style-language/styles/blob/master/apa.csl
