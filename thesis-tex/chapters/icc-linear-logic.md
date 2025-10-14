# Linear logic

## Proofs as programs (Curry–Howard correspondence)

A central insight of modern logic and type theory is that the process of proving a theorem in a particular deduction system can be thought of as a computational process, similar to executing a computer program. Similarly, when considering typed programming languages, the type of the function we are implementing corresponds to a proposition we want to prove. 

- On the *logical side*, a proof that $\Gamma \vdash A$ shows that from the assumptions listed in $\Gamma$, one can derive $A$.  
- On the *computational side*, a term $t$ with typing judgment $\Gamma \vdash t : A$ says that given inputs of the types in $\Gamma$, the program $t$ produces an output of type $A$.  

Extensive literature exists in this area, also known as the Curry–Howard correspondence. A good introduction to it is a book by S\o{}rensen and Urzyczyn: [@10.5555/1197021]. For the purposes of this thesis, we will only demonstrate it slightly more precisely by comparing the foundations of both natural deduction and lambda calculus.
The following are the axiom, introduction, and elimination rules for **intuitionistic implicational natural deduction**:

$$
\infer[\text{Ax}]
  {\Gamma, A, \Gamma' \vdash A}
  {}
$$

$$
\infer[{\to I}]
  {\Gamma \vdash A \to B}
  {\Gamma, A \vdash B}
$$

$$
\infer[{\to E}]
  {\Gamma \vdash B}
  {\Gamma \vdash A \to B \quad \Gamma \vdash A}
$$

And here are the typing rules for the **simply typed $\lambda$-calculus**:

### Lambda calculus typing

$$
\infer[\text{Var}]
  {\Gamma_1, x : A, \Gamma_2 \vdash x : A}
  {}
$$

$$
\infer[{\to I}]
  {\Gamma \vdash (\lambda x:A.\; t) : A \to B}
  {\Gamma, x:A \vdash t : B}
$$

$$
\infer[{\to E}]
  {\Gamma \vdash t\; u : B}
  {\Gamma \vdash t : A \to B \quad \Gamma \vdash u : A}
$$

Under this view:  

- Adding an axiom or hypothesis corresponds to introducing a variable.  
- Introduction rules correspond to constructing data (for example, function abstraction).  
- Elimination rules correspond to using or destructing data (for example, function application).  
- Proof normalization corresponds to program evaluation (e.g. $\beta$-reduction in $\lambda$-calculus).  

This correspondence provides a formal bridge between reasoning in logic and reasoning about computation.

## Linear types and resources

In intuitionistic logic and the simply typed $\lambda$-calculus, assumptions in the context $\Gamma$ can be freely duplicated (contraction) or ignored (weakening). This corresponds to programs that can copy or discard variables arbitrarily.

**Linear logic**, introduced by Girard, restricts these structural rules. In the corresponding $\lambda$-calculus, each variable must be used *exactly once*. This leads to **linear types**, where values are treated as *resources*:  
- A value must be consumed once (no weakening).  
- A value cannot be duplicated (no contraction).  
- The order of usage does not matter (exchange is allowed).  

Thus, linear types provide a fine-grained way to model computation where resources (such as memory cells, channels, or tokens) cannot be copied or discarded at will. This perspective opens the door to implicit control of computational complexity, since unrestricted duplication of resources is closely related to uncontrolled growth in computation.

## Modern results in Implicit Computational Complexity

<!-- For characterization of logspace-computable predicates, a variant of propositional linear logic called "parsimonious logic" was introduced in [@mazza:LIPIcs.CSL.2015.24]. Ulrich Schöpp has proposed **LogFPL**, a typed functional programming language designed to capture FLOGSPACE [@10.1007/11874683_40].  -->
In 2013, Dal Lago and Schöpp introduced **IntML**, a functional programming language with a linear type system that characterizes **FLOGSPACE** [@DALLAGO2016150]. This marked a significant milestone for Implicit Computational Complexity (ICC). An implementation of IntML is available on GitHub[^1], and to the best of my knowledge it remains the only language within the linear-logic branch of ICC that has both a working implementation and some potential for (academic) practical use.  

Despite this achievement, IntML’s complex typing rules make it difficult to translate most standard imperative algorithms into the language without substantial modification. While, in principle, the language could serve as a platform for reimplementing well-known algorithms within this new paradigm, the steep learning curve creates a significant barrier to adoption. As a result, it is unlikely to become a convenient tool for algorithm designers.  

For these reasons, we decided not to pursue IntML further and not to focus on linear type systems in this work. Instead, we turn to another language discussed in [Chapter: Recursion Theory](#icc-recursion-theory).  

[^1]: Source code: [https://github.com/uelis/IntML](https://github.com/uelis/IntML) Following my private communication with the authors, a permissive license was added to the repository, as it was not included originally.