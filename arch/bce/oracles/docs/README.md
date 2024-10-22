# About these files:
- book.md: Pandoc-style Markdown file, containing all the theory behind the
project.

## Pandoc command
pandoc -o output.md book.md -f markdown -t gfm --bibliography references.bib --filter pandoc-citeproc --csl apa.csl

## Citation style
apa
source:
https://github.com/citation-style-language/styles/blob/master/apa.csl
