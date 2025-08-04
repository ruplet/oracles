All of my work on the formaliation of bounded arithmetic has been moved to
https://github.com/ruplet/formalization-of-bounded-arithmetic



proposition 5.32 a string function is sigma0b-bit-definable iff it is in FAC0
follows from def 5.32, corollary 5.17
def 5.32:
for Phi: set of formulas (e.g. sigma0b)
string function F(x, Y) is Phi-bit-definable if is formula phi in Phi and number term t(x, Y) s.t.
F(x, Y)(i) iff i < t(x, Y) and phi(i, x, Y)
the RHS of this is a bit-defining axiom of F.

corollary 5.17: string function is in FAC0 iff is p-bounded
and its bit graph is represented by a sigma0b formula
the same holds for a  number function, with graph replacing bit-graph
proof: follows from sigma0b representation theorem 4.17

theorem 4.17: relation R(x, X) is in AC0 iff it is represented by some Sigma0b formula phi(x,X)
proof: like theorem 3.58

there are functions whose graphs are in AC0 (representable by sigma0b formulas),
but which do not belong to FAC0 (section: proof of witnessing theorem for v0)


theorem 3.58.
one side: compline LTH turing machines to formulas. we're not going to do that.
second side: Delta0n subset LTH.
bounded quantifiers correspond to exists, forall states in ATM.
only interesting case is that `R(x, y, z) iff x*y=z` is in LTH.
use corollary 3.60 which shows L subseteq LTH and that multiplication is in L.

some intuitionistic logic in lean:
https://github.com/DafinaTrufas/Intuitionistic-Logic-Lean

Bounded arithmetics in Lean:
https://github.com/FormalizedFormalLogic/Foundation

ważne: palalansouki


file:///home/maryjane/Downloads/1235421934.pdf
strona 52 pdf, strona 316 ksiazki
chapter V Bounded arithmetic
tu jest o kodowaniu CFG

Paper:
Suppose IS12 proves Exists y . A(y, c).
Then S12 proves istnieje dowod
https://mathweb.ucsd.edu/~sbuss/ResearchWeb/intuitionisticBA/intuitionisticBA_OCR.pdf
Tutaj strona 160 (58 pdfa) wykazuje conjecture 3 z powyzszego!:
https://doi.org/10.1016/0168-0072(93)90044-E
no i Godel encoding jest wazny, bo jego dowod 1 twierdzenia o niezupelnosci
to tak naprawde interpreter!

ważne: Cook and Urquhart's theory IPV

przykłady rozszerzeń arytmetyki:
https://en.wikipedia.org/wiki/Conservative_extension

hierarchia arytmetyk
https://en.wikipedia.org/wiki/Ordinal_analysis

Weak systems of arithmetic:
https://golem.ph.utexas.edu/category/2011/10/weak_systems_of_arithmetic.html

IΔ₀ and linear time hierarchy!
Elementary Function Arithmetic = EFA
Primitive Recursive Arithmetic = PRA
RCA0*
IDelta0 + Exp

Primitive recursion:
https://ftp.cs.ru.nl/CSI/CompMath.Found/week9.pdf

A constructive proof of the Gödel-Rosser incompleteness theorem has been completed using the Coq proof assistant
http://r6.ca/Goedel/goedel1.html

Redukcje w Coq różne:  jest tutaj Ackermann function, PRA
https://github.com/rocq-community/hydra-battles

Definicje e.g. arytmetyki Q Robinsona:
file:///home/maryjane/Downloads/1235421930-2.pdf

Coding of sets and sequences, strona 31 pdfa (295):
file:///home/maryjane/Downloads/1235421934.pdf
Książka:
https://projecteuclid.org/eBooks/perspectives-in-logic/Metamathematics-of-First-Order-Arithmetic/toc/pl/1235421926

Funkcja jest dowodliwa w PA wtedy i tylko wtedy gdy rośnie wystarczająco wolno!
https://math.stackexchange.com/questions/4859305/are-there-examples-of-statements-not-provable-in-pa-that-do-not-require-fast-gro?rq=1
Czyli funkcje, które są niedowodliwe, a rosną wolno (np. są 0/1), nie mogą być wyrażalne!

https://mathoverflow.net/questions/382179/what-can-i-delta-0-prove

Euler's phi function in IDelta0:
https://link.springer.com/article/10.1007/BF01375521

czym jest transfinite induction w ERA, PRA, PA:
https://mathoverflow.net/questions/123713/era-pra-pa-transfinite-induction-and-equivalences?rq=1


24. Cook-Nguyen (history):
The universal theory VPV is based on the single-sorted theory PV [39].
which historically was the first theory designed to capture polynomial time
reasoning. 

