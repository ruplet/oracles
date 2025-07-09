---
title:
- Realizing computational complexity results
author:
- Paweł Balawender
date:
- April 10, 2025
# pandoc -t beamer magisterka.md -o magisterka.pdf --bibliography references.bib --citeproc  -M link-citations=true -V colortheme:crane -V theme:CambridgeUS --csl apa.csl
---
# Motivation
- Why consider weaker programming languages? To make reasoning about them easier!
- Why consider very low complexity classes? 
    Hypothesis: they will constitute for good benchmarks of verification tools
    (since they are guaranteed to be very simple, the verification should automatize well)

# FO
- FO[+, *] = FO[BIT]
- FO[<, *] = FO[BIT] (Crane Beach Conjecture)
- FO[+] is less expressive than FO[<, *] = FO[<, /] = FO[<, COPRIME] [@10.1002/malq.200310041]

# DLOGTIME
- example of DLOGTIME reduction to show tree isomorphism for string-represented trees, is NC1-complete [@694595]

# NC0
- One-way permutations in NC0: [@10.1016/0020-01908790053-6]
- All sets complete under AC0 reductions are in fact already complete under NC0 reductions: [@10.1145/258533.258671] [@AGRAWAL1998127]
- Immerman at page 81 shows how to do addition in NC0 and MAJORITY in NC1 [@Immerman1998-IMMDC]

- Addition and substraction of binary numbers is in AC0: [@27676]
- This is not trivial, as these algorithms in NC0/AC0 use Chinese Remainder Representation or Fermat's Little Theorem!

# AC0
- Addition is in AC0 [@BussLectureNotes]
- FO[+, *] = DLOGTIME-uniform AC0 (https://complexityzoo.net/Complexity_Zoo:A#ac0)
- Discussion of DLOGTIME-uniform AC0: [@hella2023regularrepresentationsuniformtc0]
- Tutaj mamy definicje AC0, TC0, FATC0, FTC0 etc.: [@AGRAWAL2000395]

# TC0
- Multiplication is in TC0 [@BussLectureNotes], this resource cites this: [@doi:10.1137/0213028] but i cant find relevant info there

# NC1
- Division is in DLOGTIME-uniform NC1: [@ITA_2001__35_3_259_0]
- Reductions for NC1: Dlogtime!
- Reductions for NC1: UE* reductions; UE*-uniform NC1 = ALOGTIME [@RUZZO1981365]
- example of many-one NC1 reduction for L-completeness of tree isomorphism (trees repr. as pointers): [@694595]

# L
- Reductions for L: e.g. first-order reductions, Immerman 1999 p.51
- USTCONN is complete for L
- a programming language for L: a finite number of variables, each <= n
- alternative: a finite number of input pointers; this is really similar to multi-head two-way automaton [@423885] [@10.1007/BF00289513]
- a formal proof of composition in L could be of interest for formal verification

# FL
- to show FL-completeness, it suffices to show L-completeness: FL = L* = L + NC1 reductions [@COOK19852, proposition 4.1]
- examples of FL-complete problems: 

# SL
- L subset SL subset NL
- 2004: L = SL

# NL
- STCONN is FO-complete for NL, NL closed under FO reductions (https://en.wikipedia.org/wiki/First-order_reduction)

# What makes a verification problem interesting?
- VerifyThis competition! https://verifythis.github.io/onsite/cfp/ 
- Leino: https://program-proofs.com/

# Horn-satisfiability is P-complete
- https://github.com/mikolalysenko/horn-sat?tab=readme-ov-file
- Prolog should be able to do that?
- https://cs.stackexchange.com/questions/171728/is-the-functional-circuit-value-problem-fp-complete
- Interesting: Implement Horn-SAT or CVP in Dafny!
- Use simple code for calculations and ghost functions to prove correctness!

# Circuit Value Problem
- For a given single-tape, polynomial-time Turing machine `M` and input `x`, in [@Kozen2006], there is an explicit construction of a boolean circuit over (0, 1, `and`, `or`, `not`) (with fan-in 2 for `and`, `or` and 1 for `not`), with one output node, such that its value is 1 if and only if machine `M` accepts input `x`. The construction is in LOGSPACE. So CVP is P-complete w.r.t. LOGSPACE-reductions.
- This is a good example of a LOGSPACE-reduction, being a good benchmark for the LF programming language and for the circuit description language
- The problem is that we can't generate tests for it; we have no database of Turing machines descriptions
- It can be implemented using topological sorting. We have code for toposort in Dafny! [@faria2023casestudiesdevelopmentverified]
- https://github.com/joaopascoalfariafeup/DafnyProjects
- We have some code here also: https://rad.ort.edu.uy/server/api/core/bitstreams/8ed3c93c-feb3-430c-8ee2-a7ec8875fc37/content 
- Toposort in WhyML: https://github.com/Ekdohibs/why3-toposort/blob/master/topo.mlw 

# Concrete Turing Machines
- How to obtain definitions of concrete Turing machines, with transitions stated explicitly etc.?
- Small deterministic Turing machines: [@KUDLEK1996241]
- Small universal Turing machines: [@ROGOZHIN1996215]
- Verified programming of Turing machines in Coq Forster: [@10.1145/3372885.3373816]
- Formalizing Turing machines: [@10.1007/978-3-642-32621-9_1]
- Ciaffaglione's proof of halt in Coq has a Turing Machine code

# FNP class
- https://cs.stackexchange.com/questions/71617/function-problems-and-fp-subseteq-fnp
- https://cstheory.stackexchange.com/questions/37812/what-exactly-are-the-classes-fp-fnp-and-tfnp
- https://complexityzoo.net/Complexity_Zoo:F#fp

# SAT is NP-complete
- a tool can output a short witness for a 'yes' instance
- but a proof for the 'no' instance can be of exponential size!
- verified sat solver in dafny + remarks about sat solvers: https://arxiv.org/pdf/1909.01743 

# Bounded arithmetics
- https://users.math.cas.cz/~jerabek/papers/vnc.pdf

# References {.allowframebreaks}