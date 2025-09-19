# Introduction
This thesis investigates the problem of certifying computational complexity of standard computer algorithms. The most intuitive solution to it is to formalize a standard computational model (e.g. Turing machines or lambda calculus) and its notion of computational complexity in a proof assistant such as Rocq or Lean. Then, implement the algorithm in such a formalization and prove that it will e.g. execute in polynomial time. This, however, proves to be extremely difficult. The proofs from the area of computational complexity tend to be very "hand-wavy" and making them formal is orders of magnitude more involved than formalizing other areas of mathematics [forster:LIPIcs.CSL.2025.3].
As of September 2025, no feasible way of doing that on scale has been discovered.

A promising approach is to first give an “on-paper” proof that the functions in a complexity class are equivalent to the semantics of a specially designed programming language. Then, instead of repeatedly checking complexity proofs for each algorithm, we can just define the algorithms in this language. That way, we only need to manually verify the interpreter once, and afterwards we can let the interpreter automatically check whether any given program is valid.

This thesis investigates approaches to designing programming languages whose expressiveness is precisely aligned with a target computational complexity class. In such languages, every program would, by construction, operate within the given class, and conversely, any function or problem in that class would be expressible and implementable in the language.

To illustrate the challenge we are addressing, consider the task of proving that binary multiplication belongs to LOGSPACE. 
A common way to do it is to first argue that if we show a program that does it using only a finite number of variables, each of which of linear size (e.g. a pointer to the input), then the computation obviously uses only logarithmic amount of memory.
However, this description is fragile: for instance, simply incrementing a variable in a `for` loop can exceed the LOGSPACE bound. In this work, we investigate more reliable characterizations.

The ultimate goal of this thesis is to design a practical hierarchy of programming languages that precisely captures resource-bounded computations - for example, languages that express exactly the class of algorithms running in $\mathcal{O}(n^2)$ time or $\mathcal{O}(n)$ space. In the chapters that follow, we explore which restrictions of this kind are feasible, and which are not.

The structure of this work is as follows:  
- Chapter 1 reviews open sub-directions that remain unexplored, including descriptive complexity
- Chapter 2 introduces Implicit Computational Complexity (ICC).  
- Chapter 3 presents the Curry–Howard approach to ICC, focusing on IntML.  
- Chapter 4 explores the recursion-theoretic approach, focusing on Neergaard's BC.  
- Chapter 5 discusses the logical approach, drawing on my work for AITP and at INRIA.  

Among these, only the logical approach has proven scalable. The others, after extensive investigation, appear unlikely to yield systems that are practical in use.