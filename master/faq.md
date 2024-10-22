- Does it make sense to consider a category of all NP-complete problems, with morphisms as poly-time reductions between different instances?
> https://cstheory.stackexchange.com/questions/3074/a-category-of-np-complete-problems

- Term algebras are initial objects in the category of algebras over a given signature
> https://en.wikipedia.org/wiki/Term_algebra#:~:text=From%20a%20category%20theory%20perspective,all%20algebras%20in%20the%20category.

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

- Grädel's theorem: on the class of finite structures with a successor relation, the collection of polynomial-time decidable properties coincides with those expressible in the Horn-fragment of existential second-order logic
> https://cstheory.stackexchange.com/questions/869/is-there-a-logic-without-induction-that-captures-much-of-p?rq=1

- Barrington's theorem: polynomial-size bounded-width branching programs have the same computation power as Boolean formulas
> https://blog.computationalcomplexity.org/2008/11/barringtons-theorem.html

- Theory of species, derivative of a data structure, quantum field theory
> http://lambda-the-ultimate.org/node/1957

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

- How type theory is the syntax of category theory
> https://ncatlab.org/nlab/show/type+theory

- Physics, Topology, Logic and Computation: A Rosetta Stone  
  parallel execution = proofs carried out in parallel = disjoint union of cobordisms = tensor product of morphisms
> https://arxiv.org/pdf/0903.0340.pdf

- Type theory is both a logic and a computation: this is the C-H isomorphism
> https://math.stackexchange.com/a/2811256/876802

- Homotopy Type Theory should eat itself (but so far, it’s too big to swallow); related to the limitations of the expressibility of the metalanguage:
> https://homotopytypetheory.org/2014/03/03/hott-should-eat-itself/

- What is the expressibility of simply-typed lambda calculus, really?
> Complexity class: REG (https://mathoverflow.net/a/296879)  
> wtf???  
> (1. FO with arbitrary predicates = AC^0)  
> (2. FO in a signature with only the order relation = star-free languages)  
> (3. https://nguyentito.eu/2018-11-scalp.pdf - ELEMENTARY)  
> (4. tak, to jest REG: https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.23.8845&rep=rep1&type=pdf)  
> (5. depends on the input/output representation!!!  
  https://cstheory.stackexchange.com/a/52102)

- Connection between logic, category and type theory:
  * Logic: minimal logic = simply typed lambda calculus (positive, implicational fragment of intuitionistic logic)
  * Category: Cartesian closed categories
  * Type theory: finite products only so curry/uncurry enough,
  because we can construct finite products from binary products?

- Computational trilogy: programming languages, type theory and algebraic topology
> https://ncatlab.org/nlab/show/computational+trilogy


- How to find specific programs for:
  * DC (dependent choice) = quote
  * Peirce law = call/cc
  * ZF axioms = ?
  * AC = ?
  * CH = forcing
- How to program in set theory?
- What are the different sides of the computational isomorphism?
  * Lambda calculus
  * Logic
  * Formal languages
  * Complexity classes
  * Automata
  * Function algebras?
- Give examples of logic constructs leading to inconsistent systems
- How to add side-effects to Coq? A Writer monad for printing?
- Do side-effects correspond to specific axioms?
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

- Descriptive complexity theory:
  * FO + Transitive closure operator = NL, nondeterministic logarithmic space
  * FO + Least fixed point operator = P, polynomial deterministic time
  * Existential SO = NP


- Scott encoding of Algebraic Data Types in higher order functions  
  scott encoding, church encoding, functional pearls
> http://kseo.github.io/posts/2016-12-13-scott-encoding.html

- Existential types in ML / Ocaml
> Didier Remy, Type systems for programming languages  
> https://web.archive.org/web/20210506181003/http://gallium.inria.fr/~remy/mpri/cours.pdf
> https://stephenebly.medium.com/an-introduction-to-existential-types-25c130ba61a4

- One ,,while'' is enough for every while program; Kleene algebra with tests
> https://www.cs.cornell.edu/~kozen/Papers/kat.pdf  
> https://en.wikipedia.org/wiki/Structured_program_theorem  
> https://dl.acm.org/doi/pdf/10.1145/256167.256195  
> https://www.sciencedirect.com/science/article/pii/S1567832611000191  
> http://lem12.uksw.edu.pl/images/6/62/Mirkowska-II-147-165.pdf

- Closures + tail-call optimization => continuations
> https://stackoverflow.com/q/75299540/3622836

- About deriving functor in ghc
> https://byorgey.wordpress.com/2010/03/03/deriving-pleasure-from-ghc-6-12-1

- Connection of catgory theory and logic
> https://ncatlab.org/nlab/show/internal+logic

- Category theory: An abstract theory of functional programming
> https://camdar.io/static/h4t/stuff/10/categoryTheory.pdf

- Category theory in SML
> https://jeremykun.com/2013/04/07/a-sample-of-standard-ml-and-the-treesort-algorithm/

- About existential types
> https://cs.stackexchange.com/q/65746

- Encoding of GADTs in SML (very interesting gist!)
> https://gist.github.com/bobatkey/8272004

- Very informational video! Semantics of Advanced Data Types - Patricia Johann
> GADTs are not functorial  
> https://www.youtube.com/watch?v=w3n8NXaADdg

- Robert Harper: Typing First-Class Continuations in ML
> in ML, continuations might not be implementable  
> The full Damas-Milner type system is shown to be unsound in the presence of first-class continuations  
> https://www.cs.cmu.edu/~rwh/papers/callcc/popl91.pdf  
  https://www.cs.cmu.edu/~rwh/papers/callcc/jfp.pdf

- PLT Redex is a domain-specific language designed for specifying and debugging operational semantics.
> https://redex.racket-lang.org/

- Infinite sets that admit fast exhaustive search
https://www.cs.bham.ac.uk/~mhe/papers/exhaustive.pdf

- Validating OCaml soundness by translation into Coq
> https://types22.inria.fr/files/2022/06/TYPES_2022_paper_15.pdf  

- Proving ML Type Soundness Within Coq
> http://web4.ensiie.fr/~dubois/tphols00-corr.pdf

- Bayes' rule in Haskell, or why drug tests don't work
> http://www.randomhacks.net.s3-website-us-east-1.amazonaws.com/2007/02/22/bayes-rule-and-drug-tests/

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

- Outstanding! article on TK in functional programming
> A Neighborhood of Infinity: A Partial Ordering of some Category Theory applied to Haskell  
> http://blog.sigfpe.com/2010/03/partial-ordering-of-some-category.html

- Hindley-Milner isn't compatible with overloading (ad-hoc polymorphism) and subtyping

- What's difficult in Haskell but not in Scala?
> zipWithN

- What can't be typed in Haskell?
> Functions on church numerals  
> https://stackoverflow.com/questions/23995736/example-of-type-in-system-f-that-is-not-available-in-hindley-milner-type-inferen?rq=1

- Lazy vs eager evaluation doesn't matter when there is no general recursion

- Difference between let-polymorphism and beta-reduction:
> https://cstheory.stackexchange.com/a/39835

- How strong a type theory do we need?
> https://queuea9.wordpress.com/2010/01/17/how-strong-a-type-theory-do-we-need/  
> https://web.archive.org/web/20150830072419/https://queuea9.wordpress.com/2010/01/17/how-strong-a-type-theory-do-we-need/


- This is very good! Towards compositional game theory
> We introduce a new foundation for game theory based on so-called open
games. Unlike existing approaches open games are fully compositional: games
are built using algebraic operations from standard components, such as players
and outcome functions, with no fundamental distinction being made between
the parts and the whole  
> https://www.cs.ox.ac.uk/people/julian.hedges/papers/Thesis.pdf

- This is cool: Polymorphism all the way up! From System F to the Calculus of Constructions
> https://xavierleroy.org/CdF/2018-2019/2.pdf

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

- Good resource on the Curry-Howard isomorphism:
> Programming = proving? The Curry-Howard correspondence today, Xavier Leroy  
> https://xavierleroy.org/CdF/2018-2019/4.pdf

- Existential types = Abstract Data Types (ADTs)?
> https://www.ps.uni-saarland.de/courses/seminar-ws02/ExistentialTypes.slides.pdf  
> Mitchell, Plotkin 1988: "Abstract types have existential type"