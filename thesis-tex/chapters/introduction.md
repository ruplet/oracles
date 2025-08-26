# Introduction
This thesis investigates approaches to designing programming languages whose expressiveness is precisely aligned with a target computational complexity class. In such languages, every program would, by construction, operate within the given class, and conversely, any function or problem in that class would be expressible and implementable in the language.

The ultimate problem we aim to solve is to formalize proofs of computational complexity of a program.
Operating with, and proving theorems about Turing machines in Rocq is insanely difficult. This is not the way to go.
Probably a paper proof of equivalence of a complexity class with some implicit characterization, and then
formally verify the implicit characterization, is the way to go.

The holy grail of this thesis would be to create a hierarchy of programming languages, which is practical, and which only expresses e.g. n^2-time, or O(n)-space etc.
- The obvious approach: LOOP language.
problem: it is only PRA, not all of PTIME. it is not practical.
- Another obvious approach: python + polynomial expressing max
number of steps. Problem: semantics impossible to reason about.
- another obvious approach: "natural number coding nth program of a language
having these properties". problem: syntax might be undecidable! won't write an
interpreter.
- another approach: only use Nat type and grzegorczyk hierarchy. problem: ?

We try to catch and state  precisely what do we mean by a 'practical' languauge / 'clean' code. but it takes us months to state this: code is clean when it is easy to prove correct! what is the easiest way to formalize (on a computer) the proof that multiplication
of numbers is in LOGSPACE? anegdotka o moim programie w Pythonie na ZLO.
applications of this property (formalization that something is in complexity)
to cryptography. motivations of zsm, cloudflare ddos (regex).

thus: problem with grzegorczyk hierarchy: infeasible to prove that a problem will be correct, due to complicated encoding of types!

The work is organized into three main parts.

**Part I** examines whether the computational complexity of programs can be controlled by constraining the complexity of their specifications. From one side, I investigated *descriptive complexity theory*, which characterizes the complexity of decision problems—i.e., determining whether a given structure satisfies a relation—purely in terms of the logical resources needed to express that relation. While descriptive complexity does not reason about functions directly, it can indicate which specification logics correspond to particular complexity classes (for example, first-order logic with a fixed-point operator captures PTIME decision problems). 

From the other side, I explored type theory—specifically through the lens of linear logic and linear type systems—with the idea of combining it with insights from descriptive complexity. The aim was to investigate whether a programming language could be designed whose type system inherently enforces PTIME computation. While this direction did not culminate in a working prototype, I present a literature review of this area

**Part II** focuses on *Implicit Computational Complexity* (ICC), particularly techniques that limit computational power by constraining recursion. For instance, a language might forbid arbitrary recursion but permit carefully restricted recursion schemes. This approach appears to lead naturally toward practical language design. However, our attempts to build a usable language on top of existing ICC research revealed challenges: programs expressed in these paradigms differ so drastically from conventional imperative code that practicality remains doubtful.

**Part III** explores the deep analogy between restricting the expressiveness of a programming language and restricting the axioms or rules of inference in mathematics. We discuss the field of *reverse mathematics*, the bounded arithmetic theories that arise within it, and how these theories provide powerful tools for reasoning about computational complexity.

This exploration resulted from the study of two broader research questions:  

1. When should a feature be added to a programming language?
For example, if a language already has `while` loops, adding `for` loops may be mere syntactic sugar. However, if the language only supports loops of the form `for i = 1 .. n` with constant `n`, then introducing `while` loops could be the only way to allow non-terminating computation. A related  ---  and in many ways more challenging  ---  question concerns the required strength of the type system. Could a language be practical with only integer type? With just integers, strings, and functions? Is a type system necessary at all? While these considerations fall outside the primary scope of this thesis, further discussion and pointers in this direction are provided in Appendix F: *Programming Language Features*.

2. Can a feature be safely added?
Adding features while preserving semantic properties  ---  such as guaranteed termination  ---  can be subtle and error-prone. This is especially true in type systems, where seemingly minor changes may allow unsoundness, causing the type checker to incorrectly validate ill-typed programs.

While these questions are difficult to even state for programming languages, we have been studying their counterpart in logic for quite a while.  This whole branch of
my research resulted from trying to tie 'intuitionistic logic can't prove P v ~P' with
a problem not being in a given complexity class.
In Appendix : Curry-Howard, we study: aa) how lambda calculus corresponds to programming languages a) how lambda calculus constructs correspond to logical constructs (curry-howard isomorphism) b) how extending a logic with an axiom results in a different, or the same logic c) how extending a lambda calculus type theory with an axiom results in an inconsistent, or a consistent logic d) how we can study unexpressibility of a program in a programming language through known independence proofs - forcing (continuum hypothesis), kripke models, baker-gill-solovay theorem proof using oracles (oracles are like forcing)

Another line of research corresponded to breaking sterotypes about how programming languages have to be implemented. we examine the question: why is programming languages'
syntax modeled by a tree / represented with a CFG. we relate programming languages with
proof theories (tree-like vs dag-like proof systems + cirquent calculus i GoI). we analyze weakest representations, show st-connection(?) language to represent ac0 circuits in super simple reduction systems etc.
We investigate if we could first desing logic /type theory for complexity class, and then obtain nice categorial semantics of such a language through the notion of *internal logic of a category* [@nlab:internal_logic].
We try to relate lambda calculus with complexity class. analyze complexity class of STLC.
This is only in appendix.

From the other side, we investigate if we can find logic corresponding
to complexity, then design lambda calculus for it. We explore fine-grained complexity, but it is too far away. Then explore Descriptive Complexity and, again, of linear logic. Problem: descriptive complexity
is all about model theory and decision problems only...

then we find linear logic and linear type systems. Analyze linear type systems, as a good idea on how to express complexity classes. Examine Ugo dal Lago's work. deem it impractical.

Find Implicit Computational Complexity, examine different approaches, find jones work, examine Neergaard's work and deepen recursion theoretical approach. Deem it impractical.
Remark about explicit and implicit characterizations.
Remark about syntactic and semantic complexity classes.
Remark about functional and decision complexity classes + how Cook answers it precisely!
Quick remark about affinity in neergaard's algebra and circuit complexity
as a seemingly unstudied way to prove L neq P.

Examine reverse mathematics. This resulted from study of how large of sets can mathematics (ZFC) create. Find bounded arithmetic. Find IDelta0 and that it can't express exp function. Find Buss' PV theories and Cook's V^i hierachy. Look for
a way to implement / formalize results about V^i. Find a way to do it. Find a paper which requires formalization of 'provability in V^i' to construct Hoare semantics
of an imperative programming language. This is presented at AITP.

We conclude that formalization of arithmetic is a promising way to formalize
a theorem of the form 'function is in FLOGSPACE'. We examine previous approaches to
formalize turing machines in coq. We examine using Dafny to semi-formalize
complexity results by only formalizing correctness, but with specification which
is proved (on paper) to be good for a given complexity. We list Why3 and hybrid methods (Dafny vs Coq), because Dafny is a toy. We talk about Prop in Rocq and Lean and how
Prop cannot tell between quantifier-free and not-qf formulas - which is we need the
deep embedding of the logic. We talk about Rocq FOL proof mode and not examine it. We talk about mathlib ModelTheory. We show our code, which proves to be a successful way
to formalize Cook and Nguyen's V^i hierarchy by encoding two-sorted logic as single-sorted. We focus on formalizing IDelta0, as the overlap is huge and is a
prerequisite.

