---
title:
- Realizing computational complexity results
author:
- Paweł Balawender
date:
- April 10, 2025
# pandoc -t beamer magisterka.md -o magisterka.pdf --bibliography references.bib --citeproc  -M link-citations=true -V colortheme:crane -V theme:CambridgeUS --csl apa.csl
---
# Circuit Value Problem
- For a given single-tape, polynomial-time Turing machine `M` and input `x`, in [@Kozen2006], there is an explicit construction of a boolean circuit over (0, 1, `and`, `or`, `not`) (with fan-in 2 for `and`, `or` and 1 for `not`), with one output node, such that its value is 1 if and only if machine `M` accepts input `x`. The construction is in LOGSPACE. So CVP is P-complete w.r.t. LOGSPACE-reductions.
- This is a good example of a LOGSPACE-reduction, being a good benchmark for the LF programming language and for the circuit description language
- The problem is that we can't generate tests for it; we have no database of Turing machines descriptions

# Concrete Turing Machines
- How to obtain definitions of concrete Turing machines, with transitions stated explicitly etc.?
- Small deterministic Turing machines: [@KUDLEK1996241]
- Small universal Turing machines: [@ROGOZHIN1996215]
- Verified programming of Turing machines in Coq Forster: [@10.1145/3372885.3373816]
- Formalizing Turing machines: [@10.1007/978-3-642-32621-9_1]

# References {.allowframebreaks}