# Linear logic

## Proofs as programs (Curry–Howard correspondence)

A central insight of modern logic and type theory is that **proofs can be understood as programs** and **propositions as types**. This is known as the Curry–Howard correspondence. 

- On the *logical side*, a proof that $\Gamma \vdash A$ shows that from the assumptions listed in $\Gamma$, one can derive $A$.  
- On the *computational side*, a term $t$ with typing judgment $\Gamma \vdash t : A$ says that given inputs of the types in $\Gamma$, the program $t$ produces an output of type $A$.  

Under this view:  

- An axiom or hypothesis corresponds to introducing a variable.  
- Introduction rules correspond to constructing data (for example, function abstraction).  
- Elimination rules correspond to using or destructing data (for example, function application).  
- Proof normalization corresponds to program evaluation (e.g. $\beta$-reduction in $\lambda$-calculus).  

This correspondence provides a formal bridge between reasoning in logic and reasoning about computation.

---

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

And here are the corresponding rules for the **simply typed $\lambda$-calculus**:

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

---

## Linear types and resources

In ordinary intuitionistic logic and the simply typed $\lambda$-calculus, assumptions in the context $\Gamma$ can be freely duplicated (contraction) or ignored (weakening). This corresponds to programs that can copy or discard variables arbitrarily.

**Linear logic**, introduced by Girard, restricts these structural rules. In the corresponding $\lambda$-calculus, each variable must be used *exactly once*. This leads to **linear types**, where values are treated as *resources*:  
- A value must be consumed once (no weakening).  
- A value cannot be duplicated (no contraction).  
- The order of usage does not matter (exchange is allowed).  

Thus, linear types provide a fine-grained way to model computation where resources (such as memory cells, channels, or tokens) cannot be copied or discarded at will. This perspective opens the door to implicit control of computational complexity, since unrestricted duplication of resources is closely related to uncontrolled growth in computation.

## Modern results in Implicit Computational Complexity

<!-- For characterization of logspace-computable predicates, a variant of propositional linear logic called "parsimonious logic" was introduced in [@mazza:LIPIcs.CSL.2015.24]. Ulrich Schöpp has proposed **LogFPL**, a typed functional programming language designed to capture FLOGSPACE [@10.1007/11874683_40].  -->
In a major milestone for ICC, in 2013 Dal Lago and Schöpp introduced **IntML**, an implementation of a functional programming language with a linear type system that characterizes FLOGSPACE [@DALLAGO2016150]. The implementation is avalable on Github [^1]. It is the only language I have been able to find, designed within the linear-logic branch of ICC, that has received an actual implementation and can be used in (academic) practice.

However, the entry barrier to this language is relatively high, primarily due to its intricate typing rules. With sufficient introduction, the language could be used to reimplement certain well-known algorithms, but many would not transfer directly. The programming style enforced by a linear type system differs so substantially from conventional approaches that, for the purposes of this thesis, I chose instead to focus on another language discussed in [Chapter: Recursion Theory](#icc-recursion-theory).


[^1]: Source code: [https://github.com/uelis/IntML](https://github.com/uelis/IntML) Following my private communication with the authors, a permissive license was added to the repository, as it was not included originally.


