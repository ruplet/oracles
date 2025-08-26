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