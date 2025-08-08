# Linear Logic and Type Systems in Implicit Computational Complexity

Implicit Computational Complexity (ICC) seeks to characterize complexity classes using logical and syntactic restrictions, rather than by referring to machine models or explicit resource bounds. This field lies at the intersection of logic, computational complexity, and programming language theory, with foundational contributions from Bellantoni and Cook, Leivant, Marion, and Jones.

ICC is often viewed as the **proof-theoretic analogue** of descriptive complexity. While descriptive complexity uses model-theoretic tools to classify decision problems based on their logical definability, ICC approaches computational complexity from within the syntax of programming languages and type systems. Instead of defining classes via complete problems or Turing machines, ICC restricts the structure of programs or proofs to ensure that only functions in a given complexity class are expressible.

A key foundation for many ICC systems is **linear logic**, introduced by Girard. Linear logic provides a fine-grained control of duplication and erasure of data, distinguishing between resources that must be used exactly once and those that may be reused. This resource sensitivity makes linear logic particularly well-suited to express and enforce **space constraints**, and has led to several important advances in the design of type systems for space-bounded computation.

## Schöpp (2006): A Type System for Logarithmic Space  
([PDF](https://ulrichschoepp.de/Docs/seci.pdf))

Ulrich Schöpp introduces **LogFPL**, a typed functional programming language designed to capture the complexity class **LOGSPACE**. The system extends Hofmann’s LFPL (Linear Functional Programming Language) with annotations that track resource usage more precisely. The design is inspired by **Geometry of Interaction** and **game semantics**, and models computation as a form of structured dialogue between the program and its environment.

This **interactive view of computation** enables space-efficient recursion. For instance, if a function $h : \mathbb{N} \rightarrow \mathbb{N}$ has the property that each output bit depends only on a single bit of its input, then the bits of `h^k(x)` (the `k`-fold composition of `h`) can be computed one at a time, storing only a small amount of intermediate state. This avoids the need to materialize or store entire intermediate values—a crucial feature for LOGSPACE soundness.

Schöpp’s type system uses **annotations** to control how often variables can be accessed and how much memory they may consume:

- Variables annotated with $\infty$ may be queried arbitrarily many times.

- Variables annotated with `·` may be queried at most once.

Function types are similarly annotated to express how many questions a function may ask of its input and how much memory it uses in doing so. These features together enable the type system to enforce **LOGSPACE bounds** compositionally. 

## Mazza (2015): Simple Parsimonious Types and Logarithmic Space  
([PDF](https://drops.dagstuhl.de/storage/00lipics/lipics-vol041-csl2015/LIPIcs.CSL.2015.24/LIPIcs.CSL.2015.24.pdf))

Damiano Mazza advances this line of work with a **parsimonious affine type system** that characterizes LOGSPACE predicates. The logic is based on an *affine propositional system*, where contraction is restricted (i.e., duplication of variables is not allowed freely), helping to control resource usage.

This work further supports the idea that **affine and linear logics** provide natural frameworks for implicit characterizations of space complexity.

## Dal Lago & Schöpp (2016): A Functional Characterization of FLOGSPACE  
([Paper](https://www.sciencedirect.com/science/article/pii/S089054011500142X), [Code](https://github.com/uelis/IntML))

In a major milestone for ICC, Dal Lago and Schöpp introduce **IntML**, a functional programming language with a linear type system that characterizes the class **FLOGSPACE**—the class of logarithmic-space *functions*, not just decision problems.

Unlike many prior systems that characterize LOGSPACE in terms of predicates or decision properties, IntML provides a full **function-level** model. Its type system, based on linear logic, ensures that only logarithmic-space computable functions can be expressed.

However, this expressiveness comes at the cost of **practical usability**. The type system of IntML is subtle and difficult to work with in practice. Programming in the language is unintuitive for those accustomed to traditional languages, and understanding the effect of types on space usage requires a deep familiarity with linear type theory.

Due to these challenges, we chose not to pursue IntML further in this thesis. Nevertheless, in the course of corresponding with the authors, we were able to obtain a freely licensed version of the implementation. The code is now publicly available under an open license at [https://github.com/uelis/IntML](https://github.com/uelis/IntML), making it accessible for future research.

---

These systems demonstrate the power of combining **type theory** with **resource-sensitive logic** to enforce space bounds implicitly. While still challenging from a usability perspective, these approaches offer promising theoretical foundations for space-aware programming languages, and they illustrate the deep interplay between computation, logic, and complexity.

After exploring both the descriptive complexity approach and the linear-logic-based direction of implicit computational complexity—without arriving at a satisfactory framework—we turned our attention to the recursion-theoretic branch of ICC. This direction is developed further in the next chapter.
