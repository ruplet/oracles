- Here, say what fine-grained complexity is. complete problems, complexity zoo etc.

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

- About semantic and syntactic complexity classes
> An interesting difference is that PR functions can be explicitly enumerated, whereas functions in R cannot be (since otherwise the halting problem would be decidable). In this sense, PR is a "syntactic" class whereas R is "semantic."  
> https://complexityzoo.net/Complexity_Zoo:P#pr



make a language for AC0-reductions and NC0:
> It is known, however, that AC0 reductions define a strictly smaller class than polynomial-time reductions (https://en.wikipedia.org/wiki/NP-completeness#Completeness_under_different_types_of_reduction)
make language for FO-reductions to consider P-complete problems

