# Introduction
This thesis investigates approaches to designing programming languages whose expressiveness is precisely aligned with a target computational complexity class. In such languages, every program would, by construction, operate within the given class, and conversely, any function or problem in that class would be expressible and implementable in the language.

The ultimate problem we aim to solve is to find a promising way of certifying computational complexity of standard computer algorithms. The most intuitive solution to this problem is to formalize standard computational models (Turing machines or lambda calculus) and their respective complexity notions in a proof assistant such as Rocq or Lean. This, however, proves to be unexpectedly difficult and as of September 2025, no feasible way of conducting such proofs on scale has been discovered.

A promising approach is to first give an “on-paper” proof that the functions in a complexity class are equivalent to the semantics of a specially designed programming language. Then, instead of repeatedly checking complexity proofs for each algorithm, we can just define the algorithms in this language. That way, we only need to manually verify the interpreter once, and afterwards we can let the interpreter automatically check whether any given program is valid.

To illustrate the challenge we are addressing, consider the task of proving that binary multiplication belongs to LOGSPACE. One possible characterization is that LOGSPACE functions are those computable using only a finite number of linear-size binary variables. However, this description is fragile: for instance, simply incrementing a variable in a `for` loop can exceed the LOGSPACE bound. In this work, we investigate more reliable characterizations.

Such proofs are particularly significant in areas like cryptography, where complexity guarantees are crucial. Yet, almost no published algorithms currently come with formally verified proofs of complexity upper bounds.

The ultimate goal of this thesis is to design a practical hierarchy of programming languages that precisely captures resource-bounded computations - for example, languages that express exactly the class of algorithms running in $\mathcal{O}(n^2)$ time or $\mathcal{O}(n)$ space. In the chapters that follow, we explore which restrictions of this kind are feasible, and which are not.

The structure of this work is as follows:  
- Chapter 1 reviews open sub-directions that remain unexplored.  
- Chapter 2 introduces Implicit Computational Complexity (ICC).  
- Chapter 3 presents the Curry–Howard approach to ICC, focusing on IntML.  
- Chapter 4 explores the recursion-theoretic approach, focusing on Neergaard's BC.  
- Chapter 5 discusses the logical approach, drawing on my work for AITP and at INRIA.  

Among these, only the logical approach has proven promising. The others, after more extensive investigation, appear unlikely to yield systems that are practical in use.

## Background of the project

This work grew out of two broader research questions:

### When should a feature be added to a programming language?  
For instance, if a language already has `while` loops, introducing `for` loops may just amount to syntactic sugar. But if the language only supports loops of the form `for i = 1 .. n` with constant `n`, then adding `while` loops may be the only way to enable non-terminating computation.  
A related - and in many ways more challenging - question concerns the required expressive power of the type system. Could a language remain practical with only integers and function types? With just integers, strings, and functions? Is a type system necessary at all?  
In the context of this thesis, for example, if functions in our language correspond to LOGSPACE functions, then by the closure of LOGSPACE under composition we are justified in adding composition and variable substitution as language features.

### Can a feature be safely added?  
Preserving semantic properties - such as guaranteed termination - while extending a language is often subtle and error-prone. This is particularly true in type systems, where even minor changes may lead to unsoundness, causing the type checker to validate ill-typed programs.  
In the setting of this thesis, the guiding question becomes: if we add a new feature as a primitive, will it still be the case that every program expresses a LOGSPACE algorithm?

While these questions are both deep and interesting, they fall outside the scope of this thesis and will not be considered further.
