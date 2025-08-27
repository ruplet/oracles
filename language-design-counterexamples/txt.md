

# Inconsistencies in type systems {.allowframebreaks}
- eager lanuages don't have categorial products, lazy don't have coproducts [@eager]

- INRIA: extending type theory with forcing [@jaber:hal-00685150]. This paper presents an intuitionistic forcing translation for the Calculus of Constructions (CoC). proven to be correct by implementation in Coq. proving negation of the continuum hypothesis
- When using the Curry-Howard correspondence in order to obtain executable programs
from mathematical proofs, we are faced with a difficult problem : to interpret each axiom
of our axiom system for mathematics (which may be, for example, second order classical
logic, or classical set theory) as an instruction of our programming language. Excluded middle
can be interpreted as call/cc, catch/throw, try/with. Krivine interpreted the whole Zermelo-Fraenkel set theory axioms, but without axiom of choice. Then in ,,Dependent choice, ‘quote’ and the clock'', Krivine interprets the whole axiom of countable choice
- In this paper, we give an interpretation of the axiom of countable choice (and even the
slightly stronger axiom of dependent choice) in classical second order logic, as a programming instruction. Using the results of [11], the same method applies indeed in ZF set
theory. Our solution is to introduce a new instruction in $\lambda$-calculus, which uses an enumeration of $\lambda$-terms. We give two different computational interpretations and in fact
implementations, for this instruction : the first is similar to the quote instruction of LISP
and the second is given in terms of a clock. [@KRIVINE2003259]
- ML with call/cc operator is unsound [@mlcallcc]

- axiom of choice is derivable in constructive dependent type theory [@axiomchoice]

- [@10.1007/11417170_16] We show that a minimal dependent type theory based on $\Sigma$-types and equality is degenerated in presence of computational classical logic. By computational classical logic is meant a classical logic derived from a control operator equipped with reduction rules similar to the ones of Felleisen’s 
 or Parigot’s $\mu$ operators. As a consequence, formalisms such as Martin-Löf’s type theory or the (Set-predicative variant of the) Calculus of Inductive Constructions are inconsistent in presence of computational classical logic.