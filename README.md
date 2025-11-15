# Oracle-oriented programming: a proof of concept


## Latex compilation
Install [pygments for Dafny](https://github.com/Locke/pygments-dafny.git).

## Current TODO
1. Render `.md` files with random notes (category theory, rubik, sudoku) to GitHub with nice citations!

## Useful Latex commands
```
biber --tool --validate-datamodel --nolog --outfile /dev/null chapters/foundations.bib
```


## Future directions
### OEIS for theoretical computer science problem statements
- create a page like OEIS, but for important computational problems from computer science
- e.g. have csoeis.org/12345 contain concrete definition of the Circuit Value Problem
(down to single-bit contents of the Turing Machine tapes) and informations about it:
that it is P-complete, that important variants are known and studied, link to reductions
from other problems (with the reduction code explicit) etc.
- a phenomenon observed on LeetCode is to refer to problems by their indices. E.g. in
the solution of problem 123 you can write (change input this way: ..., then use the same
code as for 2718.)
- perhaps provide a nice CSES-like interface to test user's code for a problem?
- optimally, we would only accept user code in one of our **programming languages expressing complexity classes** :)
