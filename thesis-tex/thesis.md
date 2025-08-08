## Introduction

This thesis investigates approaches to designing programming languages
whose expressiveness is precisely aligned with a target computational
complexity class. In such languages, every program would, by
construction, operate within the given class, and conversely, any
function or problem in that class would be expressible and implementable
in the language.

The work is organized into three main parts.

**Part I** examines how the computational complexity of a program can be
constrained by restricting the complexity of its specification. For
example, if a function can be described in first-order logic, it can
often be implemented within a lower complexity class than one requiring
a second-order specification. This observation is the starting point of
*descriptive complexity theory*, which connects the logical complexity
of problem definitions with computational complexity classes. We explore
whether the logics from descriptive complexity could be used directly as
the type theory of a programming language, thereby yielding a language
whose expressiveness exactly captures a complexity class.

**Part II** focuses on *Implicit Computational Complexity* (ICC),
particularly techniques that limit computational power by constraining
recursion. For instance, a language might forbid arbitrary recursion but
permit carefully restricted recursion schemes. This approach appears to
lead naturally toward practical language design. However, our attempts
to build a usable language on top of existing ICC research revealed
challenges: programs expressed in these paradigms differ so drastically
from conventional imperative code that practicality remains doubtful.

**Part III** explores the deep analogy between restricting the
expressiveness of a programming language and restricting the axioms or
rules of inference in mathematics. We discuss the field of *reverse
mathematics*, the bounded arithmetic theories that arise within it, and
how these theories provide powerful tools for reasoning about
computational complexity.

This exploration resulted from the study of two broader research
questions: 1. **When should a feature be added to a programming
language?** For example, if a language already has `while` loops, adding
`for` loops may be mere syntactic sugar. However, if the language only
supports loops of the form `for i = 1 .. n` with constant `n`, then
introducing `while` loops could be the only way to allow non-terminating
computation. A related—and in many ways more challenging—question
concerns the required strength of the type system. Could a language be
practical with only integer type? With just integers, strings, and
functions? Is a type system necessary at all? While these considerations
fall outside the primary scope of this thesis, further discussion and
pointers in this direction are provided in Appendix F: *Programming
Language Features*.

2.  **Can a feature be safely added?** Adding features while preserving
    semantic properties—such as guaranteed termination—can be subtle and
    error-prone. This is especially true in type systems, where
    seemingly minor changes may allow unsoundness, causing the type
    checker to incorrectly validate ill-typed programs.

By studying these three perspectives—descriptive complexity, implicit
computational complexity, and bounded arithmetic—we aim to better
understand the theoretical and practical challenges of designing
programming languages that capture complexity classes.
