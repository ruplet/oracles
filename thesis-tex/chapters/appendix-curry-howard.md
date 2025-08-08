## Proving unprovability: Kripke semantics
- even though searching for a countermodel in Kripke semantics is completely infeasible computationally, we have a good tool for the job!
- i tested and it works, find countermodels and proofs of intuitionistic formulas. code: https://github.com/ferram/jtabwb_provers/tree/master

pytanie: czy jedynym typem w jezyku programowania moze byc int?
to by otwieralo droge do po prostu primitive recursion,
hierarchii grzegorczyka i latwej skladni

- Extending Type Theory with Forcing (INRIA, 2012)
> Implementation of forcing in Coq as a program transformation and show a proof of the negation of CH  
> https://hal.science/hal-00685150/document

- Krivine 2002: AC corresponds to a global clock in the CH correspondence
> https://www.irif.fr/~krivine/articles/quote.pdf

- About expression power of simply typed lambda calculus
> Based on discussion under: https://cstheory.stackexchange.com/q/27824  
> Hillebrand, Kanellakis 1996:  
> terms of form {0, 1}* -> Bool in STLC express precisely regular languages  
> Theorem 3.4: https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.23.8845&rep=rep1&type=pdf

- Good resource on the Curry-Howard isomorphism:
> Programming = proving? The Curry-Howard correspondence today, Xavier Leroy  
> https://xavierleroy.org/CdF/2018-2019/4.pdf

- Existential types = Abstract Data Types (ADTs)?
> https://www.ps.uni-saarland.de/courses/seminar-ws02/ExistentialTypes.slides.pdf  
> Mitchell, Plotkin 1988: "Abstract types have existential type"

- A beginner’s guide to forcing
> https://arxiv.org/pdf/0712.1320

- Forcing for dummies blogpost
> https://timothychow.net/mathstuff/forcingdum.txt

- Baker-Gill-Solovay theorem proof
> Forcing as a method to prove that something can or cannot be done using an oracle  
> https://cstheory.stackexchange.com/questions/14091/forcing-method-used-in-baker-gill-solovay-relativization-paper-and-cohens-proof  
> https://math.stackexchange.com/questions/2616541/simple-applications-of-forcing-in-recursion-theory  
> https://en.wikipedia.org/wiki/Forcing_(computability)

- This is cool: Polymorphism all the way up! From System F to the Calculus of Constructions
> https://xavierleroy.org/CdF/2018-2019/2.pdf

- How to add axiom of dependent/countable choice to classical logic?
> https://ieeexplore.ieee.org/document/6280455

- How to add dependent types to classical logic?
> Compiling with dependent types: https://www.williamjbowman.com/resources/wjb-dissertation.pdf  
> This chapter explicitly avoids control effects and dependent types to focus on type preservation. However, in general, we may want to combine the two. Herbelin (2005) shows that unrestricted use of call/cc and throw in a language with $\Sigma$ types and equality leads to an inconsistent system.  The inconsistency is caused by type dependency on terms involving control effects.  Herbelin (2012) solves the inconsistency by constraining types to depend only on negative-elimination-free (NEF) terms, which are free of effects. This restriction makes dependent types compatible with classical reasoning enabled by the control operators.

- Impredicativity of Set + excluded middle + axiom of unique choice is inconsistent
> http://pauillac.inria.fr/~herbelin/talks/cic.pdf

- Continuations must be used linearly to avoid control effects, which are known to cause inconsistency with dependent types
> https://www.williamjbowman.com/resources/wjb-dissertation.pdf

- No Continuation-passing-style translation is possible along the same lines for small $\Sigma$-types and sum types with dependent case
> https://dl.acm.org/doi/10.1145/509799.503043

- Typed Exceptions and Continuations Cannot Macro-Express Each Other
> https://link.springer.com/content/pdf/10.1007/3-540-48523-6_60.pdf

forcing zeby badac jezyki programowania: to jak oracles w computational complexity!
https://cstheory.stackexchange.com/a/14093
see here for oracle A such that NEXP^A = P^{NP^{A}}
what it means in logic when you have P^A,B vs P^A^B?
https://link.springer.com/article/10.1007/s00037-001-8190-2

- Under the Curry-Howard correspondence, natural deduction corresponds to simply typed lambda calculus
- Any inductive type can be encoded in System F as polymorphic functions  
  Parametricity is anti-classical
> https://xavierleroy.org/CdF/2018-2019/6.pdf
- Numeric functions expressible in STLC = extended polynomials
- Minimal logic + ex falso quodlibet = intuitionistic logic  
  Intuitionistic logic + excluded middle = classical logic
> https://xavierleroy.org/CdF/2018-2019/4.pdf
- Is ex falso quodlibet modeled by the exception monad?
- Glivenko, 1929: Classical logic proves Phi iff intuitionistic logic proves ~~Phi
- Type theory is both a logic and a computation: this is the C-H isomorphism

- What is the expressibility of simply-typed lambda calculus, really?
> Complexity class: REG (https://mathoverflow.net/a/296879)  
> wtf???  
> (1. FO with arbitrary predicates = AC^0)  
> (2. FO in a signature with only the order relation = star-free languages)  
> (3. https://nguyentito.eu/2018-11-scalp.pdf - ELEMENTARY)  
> (4. tak, to jest REG: https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.23.8845&rep=rep1&type=pdf)  
> (5. depends on the input/output representation!!!  
  https://cstheory.stackexchange.com/a/52102)

- How to find specific programs for:
  * DC (dependent choice) = quote
  * Peirce law = call/cc
  * ZF axioms = ?
  * AC = ?
  * CH = forcing
- Do side-effects correspond to specific axioms? (pierre marie pedrot curry howard isomorphism for dummies)
  * looping (call/cc)
  * exceptions (Markov's rule, Friedman's trick)
  * global state (~CH; forcing)
  * delimited continuations (double negation shift)
- Extending the Curry-Howard correspondence:
  * axiom: system primitive
  * soundness theorem: compiler
  * completeness theorem: debugger
  * incompleteness theorem: infinite loops
  * axiom of choice trivial in intuitionistic logic, monster in classical
> https://math.stackexchange.com/questions/2862220/curry-howard-for-an-imperative-programming-language  
> https://www.xn--pdrot-bsa.fr/slides/inria-junior-02-15.pdf

11. extended curry-howard:
  - double negation ~ first-class callbacks
  - friedman's translation ~ dynamic exeptions
  - cohen's forcing ~ global variables
  - dialectica trans. ~ scoped gotos (a la Python's yield)

