---
title:
- How to design a programming language?
author:
- Paweł Balawender
date:
- March 20, 2024
# pandoc -t beamer prezentacja.md -o prezentacja.pdf --bibliography references.bib --filter pandoc-citeproc  -M link-citations=true -V colortheme:crane -V theme:CambridgeUS
# pdftk A=inria-curryhoward.pdf B=prezentacja.pdf cat B1-7 A8-15 output out.pdf
---

# Questions to consider:
- What features does it make sense to add?
- What computational model will we execute on?
- What problems do we want to solve?
- What types do we want to work with?

# What features does it make sense to add?
- Do you need recursion when you have loops?
- Do you need `while` loops when you already have `for` loops?
- Do you need `throw/catch` when you have `call/cc`?
- Do you need Turing-completeness? do you *really* need it?
    + Turing machines are very simple objects, but it's very difficult to reason about them
    + We can't even tell if a Turing machine will finish its execution

# Why nontermination is a bad thing in a typed language
- We can construct an inhabitant
of any type $T$ ($\bot_T$, representing a computation of type $T$ which didn't terminate) by just writing a 0-ary function $f: T$ which doesn't terminate
- Category-theoretical properties of the type system break
- If you think in terms of the Curry-Howard correspondence, where the type of the function is a theorem and its body is a constructive proof of it, this logic becomes trivial

<!-- # Definition of a category
- A class of objects of the category
- A class of functions (arrows) between the objects
- An operator of composition of morphisms, which is associative and preserves identities: for every object $x$, there exists a morphism $1_x: x \rightarrow x$, s.t. for every morphism $f$, $1_b \circ f = f = f \circ 1_a$ -->

# Hask is not a category
- Informally, the objects of Hask are Haskell types, and the morphisms from objects A to B are Haskell functions of type A -> B. The identity morphism for object A is id :: A -> A, and the composition of morphisms f and g is f . g = \\x -> f (g x)
- we often hear about category theory in Haskell environment: monads, functors
- but Hask is not a nice category at all
- in the definition above, it's not even a category due to properties of `undefined` and the `seq` function

# "Platonic" Hask
> Because of these difficulties, Haskell developers tend to think in some subset of Haskell where types do not have bottom values. This means that it only includes functions that terminate, and typically only finite values. The corresponding category has the expected initial and terminal objects, sums and products, and instances of Functor and Monad really are endofunctors and monads.

# Curry-Howard correspondence
- it is a relationship between computer programs and mathematical proofs
- in logic, you start with axioms and deduction rules and combine them to construct
    proofs of more complicated theorems
- in programming, you start with basic constants and algorithmic constructions (such as a `for` loop), and
    construct more complicated transformations
- in a programming language which has a good theory, by writing a function $f: a \rightarrow b$ you prove
    an implication that if an object of type $a$ exists, then there also exists an object of type $b$
- this is utilized in advanced languages (which are often also automated theorem provers) such as Coq
    to formally verify proofs or write computer programs, which are proven to be correct

# Why does it matter?
- we can analyze systems of programming primitives and constructs in a similar way to systems of axioms and deduction rules in logic
- the question: "what features does it make sense to add to a programming language?" can be analyzed from the logical perspective, and we already have tools to work with that
- e.g. the first of Hilbert's 23 problems: deciding if the continuum hypothesis is true. It was proven to be independent of ZFC, so that either CH or its negation can be added "as a feature" to ZFC (Cohen 1963).

# Preliminary: call/cc operator
- what is a continuation? it's a special case of a callback. when a function calls back another function
as the last thing it does, then the second function is called a continuation of the first
- the 1-ary `(call/cc f)` operator takes "current continuation", (i.e. "the future of the current moment") and passes it to `f`
- this operator is very ubiquitous, but also unintuitive
- programming with `goto` is nothing when compared with `call/cc`

# call/cc: apples I

![Alt text](callcc.jpg)

# call/cc: apples II

> Here's the diagram that was left on our CS lab's whiteboard. So you're going to fetch some apples, and you grab a continuation before you begin. You wander through the forest, collecting apples, when at the end you apply your continuation on your apples. Suddenly, you find yourself where you were before you went into the forest, except with all of your apples.

# call/cc is weird
```
> (define x 0) ; dummy value - will be used to store continuation later
> (+ 2 (call/cc 
          (lambda (cc)
           (set! x cc)  ; set x to the continuation cc; namely, (+ 2 _)
           3)))         ; returns 5
5
> (x 4)                 ; returns 6
6
> (* 123 (+ 345 (* 789 (x 5))))
7
  reason: it is because (x 5) replaces the existing continuation,
          (* 123 (+ 345 (* 789 _))), with x, (+ 2 _), and returns
          5 to x, creating (+ 2 5), or 7.
```

# Type system inconsistencies "in the wild" I {.allowframebreaks}
- "ML with call/cc is unsound" (this is old, I wasn't able to reproduce)
```
to: sml-list@cs.cmu.edu
Date: Mon, 08 Jul 91 12:38:25 EDT
The Standard ML of New Jersey implementation of callcc is not
type safe, as the following counterexample illustrates:

fun left (x,y) = x;
fun right (x,y) = y;
let val later = (callcc (fn k =>
	(fn x => x,  fn f => throw k (f, fn f => ())  )))
in
	print (left(later)"hello world!\n");
	right(later)(fn x => x+2)
end

(Running this example causes the NJ compiler to fail
in unpleasant ways.)
This example illustrates that the ML core language with
polymorphism plus callcc with the typing rules:
	callcc : ('a cont -> 'a) -> 'a
	throw : 'a cont -> 'a -> 'b
is unsound.  Making callcc weakly polymorphic,
	callcc : ('1a cont -> '1a) -> '1a
rules out the counterexample, and we conjecture that
the resulting system is sound, but we currently have
no proof of this.
```

# Preliminary: dependent types
- A dependent type is a family of types which vary over the elements of some other type. E.g. types of natural numbers less than or equal to $n$, for varying $n$.
- A dependent sum type (dependent coproduct) of a dependent type ($d : D \vdash C_d : Type$) is the type whose terms are ordered pairs (d, c) with d: D, c: C_d. It's similar to the union of an indexed family, for $A = \{0, 1, \dots, 255\}$ and $B(x) = X_x$ for some family of types $X_x$, $\sum_{x: A} B(x) = X_0 + X_1 + \dots + X_{255}$

# Type system inconsistencies "in the wild" II
- [@10.1007/11417170_16] shows that unrestricted use of call/cc and throw in a language with dependent sum types and equality leads to an inconsistent system.

\ \ 

> Proposition 2. For any two variables x and y, x = y is derivable in $TT^{cc}_\Sigma$


# What we know now
- as for a computational model, usually we don't have a lot of choice - a Turing machine or a RAM machine is all that is practical
- type systems are hard. Let's focus on lists of bits for everything
- we don't want non-termination.
- same reason as unwanted non-termination, we don't want to accidentally write an $O(n^2)$ program
    for an $O(n)$ problem.
- can we write programs in such a way that the time / space complexity is obvious from the syntax?
- if we only got one, unnested `for` loop, the time is obviously linear
- what about e.g. KMP algorithm? it's linear, but doesn't seem so and requires a proof

# Implicit computational complexity
- Describes complexity classes without explicit reference to a
    machine model and to cost bounds.
- Borrows techniques and results from logic (e.g. recursion theory)
- Aims to define programming language tools enforcing resource bounds on the programs

# Capturing primitive recursion
- Primitive recursive functions: these which can be computed in a C-like programming language using only definite `for`-loops (with bound known beforehand)
- many functions are PR: addition, exponentiation, tetration, logarithm
- Ackermann function is not PR
- PR contains whole ELEMENTARY

# Capturing PTIME
- one of the most well-studied complexity classes in ICC
- we have Immerman-Vardi theorem which says that PTIME-recognizable languages are precisely these expressible in first-order logic with least fixed-point operator on an ordered structure (e.g. graphs with an order on vertices)
- if we don't have an order on the structure, the question is much harder
- so hard, it's one of the most important open problems in computer science
- equivalent to the following: can we find such a programming language, so that:
    + every program of it terminates in polynomial time
    + for every permutation of the input, it always gives the same answer?

# Functional complexity classes are much less well-studied
- for decades, computational complexity people focused on decision problems
- we (at least I) are much less interested in testing if an object satisfies a predicate
- we want to calculate functions
- we know that DFA = NFA = MSO on finite strings = regular expressions = particular monoids...
- what do we know about Finite State Transducers?
    + undecidable whether two FSTs are equivalent in general (define the same relation)
    + not always minimizable

# But there is some hope
- [@10.1007/BF01201998]: a programming language for FP
- [@JONES1999151]: a programming language for LOGSPACE, where the input is a binary string
- [@10.5555/1124427.1124430]: a family of programming languages for L, LINSPACE, P, PSPACE, ...
- [@Neergaard2004AFL]: the first programming language for LF on binary natural numbers
- [@Schpp2006SpaceefficientCB]: extension of Neergaard's work with a practical type system

# References {.allowframebreaks}
