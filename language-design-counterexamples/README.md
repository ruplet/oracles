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

