---
author:
- "Paweł Balawender"
title: Practical programming languages expressing complexity classes
link-citations: true
csl: ieee.csl
bibliography: references.bib
# header-includes:
# - \usepackage{proof}
---


# Appendix C: Type theory induced by category with sufficient structure
Computational complexity is a semantic property of a program. Since we want to reason about semantics,
it is of great interest for us for our semantics to have nice properties. A connection exists, which can be
described as follows [@nlab:relation_between_type_theory_and_category_theory]:

> Type theory and certain kinds of category theory are closely related. By a syntax-semantics duality[^3] one may view type theory as a formal syntactic language or calculus for category theory, and conversely one may think of category theory as providing semantics for type theory.

Under this correspondence, we identify the notion of proposition in logic with the notions of type in type theory and object in category theory. Similarly, logical false corresponds to empty type / initial object, truth to unit type / terminal object, conjuction to product type / product, disjunction to sum type / coproduct etc [@nlab:computational_trilogy]

For a brief overview of results in this area, we present a table of logical systems and their corresponding categories of contexts[^7].

| Internal Logic[^6] / Type Theory (Syntax) | Category of Contexts (Semantics)         |
|---------------------------------------|------------------------------------------|
| Propositional logic                   | Lindenbaum–Tarski algebra (~Kripke model) |
| Intuitionistic propositional logic    | Heyting algebra                           |
| Classical propositional logic         | Boolean algebra                           |
| Minimal logic / Simply typed lambda calculus (STLC)  | Cartesian closed category (CCC)           |



[^3]: [https://ncatlab.org/nlab/show/syntax-semantics+duality](https://ncatlab.org/nlab/show/syntax-semantics+duality)
[^6]: [https://ncatlab.org/nlab/show/internal+logic](https://ncatlab.org/nlab/show/internal+logic)
[^7]: Given a dependent type theory T, its category of contexts is the category whose objects are the types of T and morphisms $f : A \rightarrow B$ are the terms of function type $A \rightarrow B$

If we could design a category such that constructible morphisms correspond to feasible computations, then by taking the internal language of such a category, we would obtain a programming language capturing (some) complexity class.

However, complexity theory is, for now, very distant from category theory. During the exploration of this approach,
I stumbled upon discussion on stackexchange.com, regarding the problem: "Does it make sense to consider a category of all NP-complete problems, with morphisms as poly-time reductions between different instances?"[@3074]. The discussion suggested that
it doesn't make a sense to go this direction. One of the answers[@3422] introduced me to *Implicit Computational Complexity*, which turned out to be the field of research I should solely focus on since the beginning of my work.

Category theory is important for people developing e.g. type theory of Lean.
But it is, for now, too far away from providing anything for studying computational complexity.
We don't explore this connection further.


- Category theory: An abstract theory of functional programming
> https://camdar.io/static/h4t/stuff/10/categoryTheory.pdf

- Dissecting / differentiating a data structure
> https://personal.cis.strath.ac.uk/conor.mcbride/Dissect.pdf

- Category theory in SML
> https://jeremykun.com/2013/04/07/a-sample-of-standard-ml-and-the-treesort-algorithm/

- Outstanding! article on TK in functional programming
> A Neighborhood of Infinity: A Partial Ordering of some Category Theory applied to Haskell  
> http://blog.sigfpe.com/2010/03/partial-ordering-of-some-category.html

- Physics, Topology, Logic and Computation: A Rosetta Stone  
  parallel execution = proofs carried out in parallel = disjoint union of cobordisms = tensor product of morphisms
> https://arxiv.org/pdf/0903.0340.pdf

- Theory of species, derivative of a data structure, quantum field theory
> http://lambda-the-ultimate.org/node/1957
> http://web.archive.org/web/20250424160632/http://lambda-the-ultimate.org/node/1957

- Term algebras are initial objects in the category of algebras over a given signature
> https://en.wikipedia.org/wiki/Term_algebra#:~:text=From%20a%20category%20theory%20perspective,all%20algebras%20in%20the%20category.





@MISC {3074,
    TITLE = {A category of NP-complete problems?},
    AUTHOR = {Paul Allen Grubbs (https://cstheory.stackexchange.com/users/2267/paul-allen-grubbs)},
    HOWPUBLISHED = {Theoretical Computer Science Stack Exchange},
    NOTE = {URL:https://cstheory.stackexchange.com/q/3074 (version: 2010-11-17)},
    EPRINT = {https://cstheory.stackexchange.com/q/3074},
    URL = {https://cstheory.stackexchange.com/q/3074}
}

@MISC {3422,
    TITLE = {A category of NP-complete problems?},
    AUTHOR = {Neel Krishnaswami (https://cstheory.stackexchange.com/users/657/neel-krishnaswami)},
    HOWPUBLISHED = {Theoretical Computer Science Stack Exchange},
    NOTE = {URL:https://cstheory.stackexchange.com/q/3422 (version: 2010-11-30)},
    EPRINT = {https://cstheory.stackexchange.com/q/3422},
    URL = {https://cstheory.stackexchange.com/q/3422}
}

@misc{nlab:computational_trilogy,
  author = {{nLab authors}},
  title = {computational trilogy},
  howpublished = {\url{https://ncatlab.org/nlab/show/computational+trilogy}},
  note = {\href{https://ncatlab.org/nlab/revision/computational+trilogy/42}{Revision 42}},
  month = aug,
  year = 2025
}

@misc{nlab:relation_between_type_theory_and_category_theory,
  author = {{nLab authors}},
  title = {relation between type theory and category theory},
  howpublished = {\url{https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory}},
  note = {\href{https://ncatlab.org/nlab/revision/relation+between+type+theory+and+category+theory/92}{Revision 92}},
  month = aug,
  year = 2025
}
