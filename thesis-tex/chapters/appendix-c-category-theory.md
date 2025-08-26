# Appendix C: Type theory induced by category with sufficient structure
Computational complexity is a semantic property of a program. Since we want to reason about semantics,
it is of great interest for us for our semantics to have nice properties. A connection exists, which can be
described as follows:

> Type theory[^1] and certain kinds of category theory[^2] are closely related. By a syntax-semantics duality[^3] one may view type theory as a formal syntactic[^4] language or calculus for category theory, and conversely one may think of category theory as providing semantics[^5] for type theory.

| Internal Logic[^6] / Type Theory (Syntax) | Category of Contexts (Semantics)         |
|---------------------------------------|------------------------------------------|
| Propositional logic                   | Lindenbaum–Tarski algebra (~Kripke model) |
| Intuitionistic propositional logic    | Heyting algebra                           |
| Classical propositional logic         | Boolean algebra                           |
| Minimal logic[^7] / Simply typed lambda calculus (STLC)  | Cartesian closed category (CCC)           |

[^1]: https://ncatlab.org/nlab/show/type+theory
[^2]: https://ncatlab.org/nlab/show/category+theory
[^3]: https://ncatlab.org/nlab/show/syntax-semantics+duality
[^4]: https://ncatlab.org/nlab/show/syntax
[^5]: https://ncatlab.org/nlab/show/categorical+semantics
[^6]: https://ncatlab.org/nlab/show/internal+logic
[^7]: https://ncatlab.org/nlab/show/minimal+logic

If we could design a category such that constructible morphisms correspond to feasible computations, then by taking the internal language of such a category, we would obtain a programming language capturing (some) complexity class.

However, complexity theory is, for now, very distant from category theory. During the exploration of this approach,
I stumbled upon discussion on stackexchange.com, regarding the problem: "Does it make sense to consider a category of all NP-complete problems, with morphisms as poly-time reductions between different instances?"[^8]. The discussion suggested that
it doesn't make a sense to go this direction. One of the answers introduced me to *Implicit Computational Complexity*, which turned out to be the field of research I should solely focus on since the beginning of my work.

[^8]: https://cstheory.stackexchange.com/q/3074

Category theory is important for people developing e.g. type theory of Lean.
But it is, for now, too far away from providing anything for studying computational complexity.
We don't explore this connection further.