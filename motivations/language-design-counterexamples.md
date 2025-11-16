- One ,,while'' is enough for every while program; Kleene algebra with tests
> https://www.cs.cornell.edu/~kozen/Papers/kat.pdf  
> https://en.wikipedia.org/wiki/Structured_program_theorem  
> https://dl.acm.org/doi/pdf/10.1145/256167.256195  
> https://www.sciencedirect.com/science/article/pii/S1567832611000191  
> http://lem12.uksw.edu.pl/images/6/62/Mirkowska-II-147-165.pdf

- Closures + tail-call optimization => continuations
> https://stackoverflow.com/q/75299540/3622836

- Barrington's theorem: polynomial-size bounded-width branching programs have the same computation power as Boolean formulas
> https://blog.computationalcomplexity.org/2008/11/barringtons-theorem.html
> https://math.stackexchange.com/a/2811256/876802

- How strong a type theory do we need?
> https://queuea9.wordpress.com/2010/01/17/how-strong-a-type-theory-do-we-need/  
> https://web.archive.org/web/20150830072419/https://queuea9.wordpress.com/2010/01/17/how-strong-a-type-theory-do-we-need/

fajna prezentacja o cbv vs cbn vs beta-reduction lambda calculus
https://groups.seas.harvard.edu/courses/cs152/2021sp/lectures/sld07-lambdacalc.pdf

- z tego co rozumiem, teoria typów jest logiką. jeśli dodamy do niej odpowiednik
   typu niedeterministycznego, np. monady List, to dla logiki wyrażającej uprzednio
   języki regularne, nic nie powinno się zmienić (DFA = NFA), ale dla logiki
   wyrażającej języki bezkontekstowe, siła wyrazu powinna się zwiększyć (DPDA < PDA)

- Should your specification language be typed? https://lamport.azurewebsites.net/pubs/lamport-types.pdf







http://beza1e1.tuxen.de/articles/accidentally_turing_complete.html
- Herbelin paradox:
   +  Herbelin, 2005: unrestricted use of `call/cc` and `throw` in a language with dependent sum types and equality leads to an inconsistent system.
   + In a paper from 2012, Herbelin gives restrictions on types that make dependent types compatible with classical reasoning introduced by call/cc
   + Bowman 2018: Herbelin (2005) shows that unrestricted use of call/cc and throw in a language with Σ types and equality leads to an inconsistent system.  The inconsistency is caused by type dependency on terms involving control effects.  Herbelin (2012) solves the inconsistency by constraining types to depend only on negative-elimination-free (NEF) terms, which are free of effects. This restriction makes dependent types compatible with classical reasoning enabled by the control operators.
   + page 175 here: https://www.williamjbowman.com/resources/wjb-dissertation.pdf

- Very interesting: You can implement SK calculus in Haskell's type system and write something,  
  which type inference of doesn't terminate! ($\Omega$)
> https://stackoverflow.com/a/34003628/3622836

- Very cool paper on type inference: 2-4-2 / Type systems Simple types, Francois Pottier
> http://gallium.inria.fr/~fpottier/mpri/cours01.pdf

- Principal type property

- ML with call/cc is unsound
> https://www.cis.upenn.edu/~bcpierce/types/archives/1991/msg00034.html

- Godel's incompleteness theorem:
> https://stackoverflow.com/a/21437375/3622836  
> We can't have a type system, which will be sound, complete and have a decidable typechecker

- Robert Harper: Typing First-Class Continuations in ML
> in ML, continuations might not be implementable  
> The full Damas-Milner type system is shown to be unsound in the presence of first-class continuations  
> https://www.cs.cmu.edu/~rwh/papers/callcc/popl91.pdf  
  https://www.cs.cmu.edu/~rwh/papers/callcc/jfp.pdf

- Scott encoding of Algebraic Data Types in higher order functions  
  scott encoding, church encoding, functional pearls
> http://kseo.github.io/posts/2016-12-13-scott-encoding.html

- Existential types in ML / Ocaml
> Didier Remy, Type systems for programming languages  
> https://web.archive.org/web/20210506181003/http://gallium.inria.fr/~remy/mpri/cours.pdf
> https://stephenebly.medium.com/an-introduction-to-existential-types-25c130ba61a4

- About existential types
> https://cs.stackexchange.com/q/65746

- Encoding of GADTs in SML (very interesting gist!)
> https://gist.github.com/bobatkey/8272004

- PLT Redex is a domain-specific language designed for specifying and debugging operational semantics.
> https://redex.racket-lang.org/

- Validating OCaml soundness by translation into Coq
> https://types22.inria.fr/files/2022/06/TYPES_2022_paper_15.pdf  

- Proving ML Type Soundness Within Coq
> http://web4.ensiie.fr/~dubois/tphols00-corr.pdf

- important book by Benjamin C. Pierce: Types and Programming Languages
> https://www.cis.upenn.edu/~bcpierce/tapl/

- Complete and Decidable Type Inference for GADTs
> GADTs have proven to be an invaluable language extension, for
ensuring data invariants and program correctness among others.
Unfortunately, they pose a tough problem for type inference: we
lose the principal-type property, which is necessary for modular
type inference.  
> https://www.microsoft.com/en-us/research/uploads/prod/2016/02/outsidein-icfp09.pdf

- Simple unification-based type inference for GADTs
> Type inference for GADTs, like in Haskell but simple:  
> https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/gadt-pldi.pdf

- Coq type inference is not known to be decidable but seems so

- Generalized Algebraic Data Types (Jones, Washburn, Weirich)
> https://www.cis.upenn.edu/~sweirich/talks/GADT.pdf

- On Understanding Types, Data Abstraction, and Polymorphism
> http://lucacardelli.name/papers/onunderstanding.a4.pdf


- Hindley-Milner isn't compatible with overloading (ad-hoc polymorphism) and subtyping

- What's difficult in Haskell but not in Scala?
> zipWithN

- What can't be typed in Haskell?
> Functions on church numerals  
> https://stackoverflow.com/questions/23995736/example-of-type-in-system-f-that-is-not-available-in-hindley-milner-type-inferen?rq=1

- Lazy vs eager evaluation doesn't matter when there is no general recursion

- Difference between let-polymorphism and beta-reduction:
> https://cstheory.stackexchange.com/a/39835

8. wymagania z JPP vs utrata wlasnosci jezyka po dodaniu do niego feature'ow
  - sml + continuations unsound
  - adding gadts breaks Principal-type property, which is necessary for modular type inference






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






 @online {
    eager,
    author = {James Iry},
    title = {Why Eager Languages Don't Have Products},
    url = {https://james-iry.blogspot.com/2011/05/why-eager-languages-dont-have-products.html},
}


@inproceedings{jaber:hal-00685150,
  TITLE = {{Extending Type Theory with Forcing}},
  AUTHOR = {Jaber, Guilhem and Tabareau, Nicolas and Sozeau, Matthieu},
  URL = {https://hal.science/hal-00685150},
  BOOKTITLE = {{LICS 2012 : Logic In Computer Science}},
  ADDRESS = {Dubrovnik, Croatia},
  HAL_LOCAL_REFERENCE = {ACTI},
  PAGES = {0-0},
  YEAR = {2012},
  MONTH = Jun,
  PDF = {https://hal.science/hal-00685150/file/forcing_lics.pdf},
  HAL_ID = {hal-00685150},
  HAL_VERSION = {v1},
}

@article{KRIVINE2003259,
title = {Dependent choice, ‘quote’ and the clock},
journal = {Theoretical Computer Science},
volume = {308},
number = {1},
pages = {259-276},
year = {2003},
issn = {0304-3975},
doi = {https://doi.org/10.1016/S0304-3975(02)00776-4},
url = {https://www.sciencedirect.com/science/article/pii/S0304397502007764},
author = {Jean-Louis Krivine}
}

@online{mlcallcc,
title={ML with callcc is unsound},
author={Robert Harper},
year={1991},
url={https://www.cis.upenn.edu/~bcpierce/types/archives/1991/msg00034.html}
}

@online{axiomchoice,
title={The Axiom of Choice in Type Theory},
year={2021},
author={John L. Bell},
url={https://plato.stanford.edu/entries/axiom-choice/choice-and-type-theory.html}}

@InProceedings{10.1007/11417170_16,
author="Herbelin, Hugo",
editor="Urzyczyn, Pawe{\l}",
title="On the Degeneracy of $\Sigma$-Types in Presence of Computational Classical Logic",
booktitle="Typed Lambda Calculi and Applications",
year="2005",
publisher="Springer Berlin Heidelberg",
address="Berlin, Heidelberg",
pages="209--220",
abstract="We show that a minimal dependent type theory based on $\Sigma$-types and equality is degenerated in presence of computational classical logic. By computational classical logic is meant a classical logic derived from a control operator equipped with reduction rules similar to the ones of Felleisen's {\$}{\{}{\backslash}mathcal C{\}}{\$}or Parigot's $\mu$ operators. As a consequence, formalisms such as Martin-L{\"o}f's type theory or the (Set-predicative variant of the) Calculus of Inductive Constructions are inconsistent in presence of computational classical logic. Besides, an analysis of the role of the $\eta$-rule for control operators through a set-theoretic model of computational classical logic is given.",
isbn="978-3-540-32014-2"
}

