# Programming languages expressing LOGSPACE
importance of logspace: need language for FL to define L-reductions to prove NP-completeness!
for p-completeness, fo/ac0 reductions are used..
In computational complexity theory, L (also known as LOGSPACE or DLOGSPACE) is the complexity class containing decision problems
that can be solved by a deterministic Turing machine using a logarithmic amount of writable space w.r.t the size (in bits)
of the input.

FL is the class of function problems computable in logarithmic space. Can we design a programming language
expressing precisely FL, i.e. any FL function will be expressible in the language, and at the same time
any function expressible in this programming language will, by design of the language, operate in logspace?

- I have obtained the code from the author, refurbished it (ported from Moscow ML to SML/NJ) and found a second, unpublished paper that clarifies a lot in the original paper
- code for Neergaard is there: https://github.com/ruplet/neergaard-logspace-characterization
- for Neergaard, I also have a proof that the function `shiftR` from his published paper is not implementable (typo, need to reverse arguments). The proof is already in `thesis-tex/main.tex`, not copying it here
- I thought for a while if a port of Neergaard's code to a modern implementation of ML would be of use. I ended up just porting to SML/NJ, as it is relatively easy to install (instructions from modern linux: https://github.com/spamegg1/unix-sml)
- https://cakeml.org/ CakeML is very interesting. It has formalized semantics and wins many awards! In particular, at POPL 2024, the paper from POPL 2014 that introduced CakeML, received the Most Influential POPL Paper Award! But I gave up on porting Neergaard's code to CakeML.
- Some links to documentation of **the** version of SML used; I needed them to modify Neergaard's code:
- https://smlfamily.github.io/Basis/array.html#SIG:ARRAY.foldri:VAL
- https://www.cs.princeton.edu/~appel/smlnj/basis/array.html
- https://www.cs.princeton.edu/~appel/smlnj/basis/aggregates-chapter.html#array-vector-slice
- https://smlfamily.github.io/Basis/vector.html#SIG:VECTOR.mapi:VAL
- SML online: https://sosml.org/editor?0&

- we have an interpreter and examples for the programming language invented by Ugo dal Lago and Ulrich Schopp (based on linear logic) there: https://github.com/uelis/IntML
- we have just a tiny bit of Haskell code written by me to define Neergaard's language and re-write the function proposed in his paper into working, formal implementations in this folder (app/ subdirectory) 

- koncepcja: różnica między algebrą BCeps- a BC jest taka, że BCeps- "wymaga"
  re-obliczania podwyrażeń po zrobieniu na nich ifa. To jest insight za L neq P

notatki z Neergaarda:
lemat:
jesli dla kazdej wartosci y, g(x:y) zwraca to samo,
oraz dla kazdego y, f(b, x: y) zwraca to samo,
to rekurencja f(n, x: y) dla kazdego y zwraca to samo.

analogiczny lemat dla zlozenia funkcji

jesli nie uzywamy cond(:y, ., .), to wynik ''nie wymaga
rozpakowywania y''

dla ustalonej funkcji f i argumentu x, ksztalt drzewa obliczen f(x : y)
moze zalezec co najwyzej od jednego bitu y:
jesli bedziemy testowac bit 0 y, to testujemy tylko parzystosc y
jesli bedziemy testowac bit 1 y, to musimy najpierw uciąć na siłe bit 0,
 zatem wynik dla [], [1], MSB[100]LSB, [101], [1001], [1000], [1100], [1101] beda takie same
 oraz dla [10], [11], [110], [111], [1010], [1011], [1110], [1111]

przechodzimy od argumentu y drzewo obliczen. na sciezce znajda sie jakies wierzcholki
p, jakies pi, jakies s i jakies cond. po wierzcholku cond, bity y nie przezywaja,
ale rezultat bedzie zalezec od jakiegos y_i, gdzie i to dokladnie liczba wierzcholkow p,
ktore ''usmiercily'' ktorys bit y (tj. nie byly poprzedzone jakims S).

drzewo obliczen: rozpatrujemy osobno wszystkie bity argumentow, zaczynamy od wierzcholkow
$x_^{(1)}_1 x^{(1)}_2, ..., x^{(n)}_1, ..., y^{(m)}_k$

na pozycjach bezpiecznych bedzie zawsze tylko podzbior oryginalnych y i stale.
liczba tych stalych moze zalezec od argumentu normalnego.

wazny paper w kwestii przegladu literatury:
https://link.springer.com/article/10.1007/BF01202288#preview
Function-algebraic characterizations of log and polylog parallel time

Damiano mazza:
Simple Parsimonious Types and Logarithmic Space
https://drops.dagstuhl.de/storage/00lipics/lipics-vol041-csl2015/LIPIcs.CSL.2015.24/LIPIcs.CSL.2015.24.pdf



- Neil D. Jones: LOGSPACE and PTIME characterized by programming languages
> https://core.ac.uk/download/pdf/82651296.pdf

- Bonfante: Some programming languages for LOGSPACE and PTIME
> https://inria.hal.science/inria-00105744/document

- Martin Hofmann: Programming Languages for Logarithmic Space 2006
> https://www-lipn.univ-paris13.fr/~baillot/GEOCAL06/SLIDES/Hofmann1302.pdf

- Kristiansen, Voda 2005: languages for LOGSPACE, LINSPACE, P, PSPACE etc.
> https://www.researchgate.net/publication/220673222_Programming_Languages_Capturing_Complexity_Classes

- Kristiansen: Neat function algebraic characterizations of logspace and linspace
> https://link.springer.com/article/10.1007/s00037-005-0191-0

- Neil D. Jones: Cons-free Programs and Complexity Classes between LOGSPACE and PTIME
> https://arxiv.org/pdf/2008.02932

- Term rewriting characterisation of LOGSPACE for finite and infinite data
> https://www.mimuw.edu.pl/~lukaszcz/logspace.pdf

- Isabel Oitavem 2010: Logspace without bounds
> provides recursion-theoretic characterization of FLOGSPACE, similar to Clote and Takeuti  
> these have explicit bounds in the recursion schemes: Cobham: FP, Thompson: PSPACE, Clote and Takeuti: NC, LOGSPACE  
> https://www.degruyter.com/document/doi/10.1515/9783110324907.355/html

- A Functional Language for Logarithmic Space, Neergaard 2004
> https://link.springer.com/chapter/10.1007/978-3-540-30477-7_21

- Cloute, Takeuti: Recursion-theoretic characterization of complexity classes
> AC0(2), AC0(6), Flogspace - also with explicit bounds!
> page 163 pdf: https://link.springer.com/chapter/10.1007/978-1-4612-2566-9_6


- Lind, Meyer 1973: A characterization of log-space computable functions
> This paper sucks, requires explicit bound on output size (log-bounded recursion on notation)  
> https://dl.acm.org/doi/pdf/10.1145/1008293.1008295

- Murawski, Ong 2004: define BC- class
> https://core.ac.uk/download/pdf/82378545.pdf

- Schopp: historia LOGSPACE
> https://ulrichschoepp.de/Docs/csl06.pdf

- Lind characterizes FLOGSPACE (1974)
> the paper sucks! log-bounded recursion!
> https://dspace.mit.edu/handle/1721.1/148880


- About BCe- algebra; Space-efficiency and the Geometry of Interaction, Ulrich Schopp
> About programming languages capturing logarithmic space
> https://www-lipn.univ-paris13.fr/~baillot/GEOCAL06/SLIDES/Schoepp.pdf

