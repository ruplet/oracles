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

- A beginner’s guide to forcing
> https://arxiv.org/pdf/0712.1320

- Forcing for dummies blogpost
> https://timothychow.net/mathstuff/forcingdum.txt

- Baker-Gill-Solovay theorem proof
> Forcing as a method to prove that something can or cannot be done using an oracle  
> https://cstheory.stackexchange.com/questions/14091/forcing-method-used-in-baker-gill-solovay-relativization-paper-and-cohens-proof  
> https://math.stackexchange.com/questions/2616541/simple-applications-of-forcing-in-recursion-theory  
> https://en.wikipedia.org/wiki/Forcing_(computability)

- Digression:
> Second-order logic is hard, because it requires processing very complicated sets. Maybe it'd be easier if these complicated sets were given by their "generators"?

- Digression:
> when data on input is in a convenient form, a reduction is in L, but if it the input is just represented as a natural number (because every countable sequence can be numbered), no efficient algorithm exists (try proving that the algorithm would probably have to 'unpack' the structure, i.e. construct the actual structure, which it is unable to because of the memory limit)

- Simone Martini: On Implicit Computational Complexity
> https://www.cs.unibo.it/~martini/BISS/martini-1.pdf  
> https://www.cs.unibo.it/~martini/BISS/martini-2.pdf  
> https://www.cs.unibo.it/~martini/BISS/martini-3.pdf  
> https://www.cs.unibo.it/~martini/BISS/  

- Simona Ronchi Della Rocca 2019: Logic and Implicit Computational Complexity
> http://panhellenic-logic-symposium.org/12/slides/Day1_Ronchi.pdf  

- Why P and L are important and robust complexity classes
> The smallest class containing linear time and closed under subroutines is P. The smallest class containing log space and closed under subroutines is still log space. So P and L are the smallest robust classes for time and space respectively which is why they feel right for modeling efficient computation.  
> https://cstheory.stackexchange.com/a/3448/71933

- Neil D. Jones: Constant Time Factors Do Matter
> NLIN-complete problem  
> https://dl.acm.org/doi/pdf/10.1145/167088.167244

- Gurevich, Shelah: Nearly linear time
> couple problems with defining DTIME(n) (dependency on computational model)  
> nearly-linear-time-complete problem under QL reductions  
> https://link.springer.com/content/pdf/10.1007/3-540-51237-3_10.pdf

- On Syntactic and Semantic Complexity Classes
> Anuj Dawar  
> University of Cambridge Computer Laboratory  
> Spitalfields Day, Isaac Newton Institute, 9 January 2012  
> https://www.newton.ac.uk/files/seminar/20120109163017301-152985.pdf  
> e.g. NP = ESO (Fagin 1974), so NP is syntactical  
> major open problem:  
> Does P admit a syntactic characterisation?  
> Can the class P be “built up from below” by finitely many operations?  
> If a complexity class C has a complete problem L, it is a syntactic class.  
> because we can enumerate all AC0 reductions  
> Two Possible Worlds:
> Either
> - there is no effective syntax for inv-P
> - there is no classification possible of polynomial-time graph problems
> - there is an inexhaustible supply of efficient algorithmic techniques to be discovered
> - P neq NP
> Or,
> - there is an effective syntax for inv-P
> - there is a P-complete graph problem under FO-reductions
> - all polynomial-time graph problems can be solved by easy variations of one algorithm.

- Leivant article: Ramified Recurrence and Computational Complexity I: Word Recurrence and Poly-time
> https://link.springer.com/chapter/10.1007/978-1-4612-2566-9_11#preview

- A descriptive complexity approach to the linear hierarchy
> https://hal.science/hal-01981070

- About semantic and syntactic complexity classes
> An interesting difference is that PR functions can be explicitly enumerated, whereas functions in R cannot be (since otherwise the halting problem would be decidable). In this sense, PR is a "syntactic" class whereas R is "semantic."  
> https://complexityzoo.net/Complexity_Zoo:P#pr

- Physical aspects of the foundational model
> What is the physical nature of computation?  
> Church-Turing thesis only relates to N->N functions.  
> Turing machines operating on real numbers are hypercomputation  
> Malament-Hogarth spacetime; relativistic Turing machines, that can
> peek into the future
> https://plato.stanford.edu/entries/computation-physicalsystems/

- Digression:
> conversion of MSO to NFA is non-elementary, but NFA to MSO is linear-time  
> what are the best data representations?  
> what about languages over the unary alphabet?  
> are there np-hard languages over the unary alphabet?  
> can the only data type in the language be {1^n: n in Nat}?  
> it seems natural that the data type for computers is { {0,1}^n: n in Nat},  
> but for set-theory based mathematics, it's Set = Empty | {Set},  
> where {} stands for... a set. So like a list, but with no order and no duplicates

- Computing aspects of set theory, Erwin Engeler ETH Zurich
> https://people.math.ethz.ch/~engeler/computing_aspects.pdf

- About the computational content of set theory
https://terrytao.wordpress.com/2010/03/19/a-computational-perspective-on-set-theory/

- Can a specific graph theory be a foundations of mathematics?
> https://mathoverflow.net/q/397581

- Comparing set theory, type theory and category theory as foundations
> https://philosophy.stackexchange.com/questions/87027/set-theory-vs-type-theory-vs-category-theory

- What do we want a foundation to be?
> What do we want a foundation to do? Comparing set-theoretic, category-theoretic, and univalent approaches  
> https://sites.socsci.uci.edu/~pjmaddy/bio/What%20do%20we%20want%20-%20final

- About different theories for foundations of mathematics
> https://mathoverflow.net/questions/364228/are-categories-special-foundationally  
> https://mathoverflow.net/questions/8731/categorical-foundations-without-set-theory  
> https://mathoverflow.net/questions/360578/category-theory-and-set-theory-just-a-different-language-or-different-foundati  
> https://mathoverflow.net/questions/352298/could-groups-be-used-instead-of-sets-as-a-foundation-of-mathematics?noredirect=1&lq=1  
> https://mathoverflow.net/questions/24773/why-do-categorical-foundationalists-want-to-escape-set-theory  
> https://mathoverflow.net/questions/9269/category-of-categories-as-a-foundation-of-mathematics