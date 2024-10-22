---
title:
- Oracle-oriented programming
author:
- Paweł Balawender
theme:
- Warsaw
date:
- March 18, 2024

---
# What's it about?
- One year ago, I was tasked with implementing an interpreter for a programming language
- I could define the programming language by myself
- But what features does it make sense to add to a programming language?
- What primitives, inexpressible in the language itself, should it contain?
- What should be the type system of it? Or should it be untyped?

# Digression: Theorems for free
- if a function has a polymorphic type, there are theorems which it has to trivialy satisfy
- e.g. a function f: Forall X, [X] -> [X], i.e. a function which for any type X, takes a
  list of X and returns a list of X, cannot really ,,look'' at the specific values 
  present in the list. it can only rearrange such lists.
- parametric polymorphism: ,,one function body, independent of the input type''
- contrasted with ad-hoc polymorphism, such as polymorphism in C++ (there may be
  many functions, behaving totally different, depending on the input type)
- assuming parametric polymorphism, there are not many functions of the type Forall X, X -> X.
  indeed, there is only one: the identity function
- Wadler's original paper: [@10.1145/99370.99404]

# The strongest case: utilizing theorems for free
- in a language weak enough, for a function with a type general enough, many
  useful theorems can be derived automatically
- sometimes it implies that there is only one function satisfying our conditions
- by building on Wadler's work, we could gain advantage in proving the
  behaviour of a function (i.e. what it really returns)

# Strong case: minimization; simple programs are simple {.allowframebreaks}
- for programs simple enough, such as representing a DFA, a minimization is possible
- that's the ultimate case of compiler optimization - we're guaranteed
  that a single minimal automaton exists which computes our function {0,1}\* -> Bool
- for the more general case of finite-state transducers, we can't always minimize
- FST minimization sometimes possible [@18919]
- nondeterministic FST are closed under composition: [@FSTcompositionclosed]
- example programming language for FST: [@DBLP:conf/fsmnlp/Schmid05]
- two-way transducers are stronger that one-way transducers (they are equivalent to mso-transductions of strings): [@filiot2013twoway]
- but two-way automata are equal to one-way automata: [@142760]
- and DSPACE(o(log log n)) = REG [@71799]

# Main case: resource utilization guarantees
- main focus of my work
- we don't want to read proofs that some program terminates in polynomial time
- we want it guaranteed by the design of the programming language
- if you only use loops of the form ,,for i=1 to n'', with n known
  before the loop and not modifying i nor n explicitly in the loop,
  every program will terminate in polynomial time, trivially
- very difficult to write programs in this form; not practical
- this is primitive recursion. Ackermann function not possible to implement
- Grzegorczyk hierarchy provides a nice classification of these functions,
  but not much known about how it relates to Turing machines-defined computational classes

# Weakest case: program termination
- almost all programs should terminate, really
- special case: implementing a HTTP server
- in Agda, programs need to be total:
- recursive programs must termiante
- for corecursive programs, any finite observation needs to return an answer in a finite time [@stackoverflow52793218]

# What's the deal with weak programming languages?
- it's ok

# About a language for FNP {.allowframebreaks}
- NP is characterized by existential second-order logic
- what about functional NP?
- FSAT (provide a witness for satisfiability) can be PTIME-reduced to SAT:
- ,,is phi with x_0=0 satisfiable? if so, x_0=0 ...''
- can every NP search problem be reduced to a corresponding NP decision problem?
- major open problem. All NP-complete search problems reduce to their decision problems (source: complexity zoo: FNP)
- e.g. checking if number is prime is ptime, but factorizing is conjectured to be NP-intermediate [@kabanets]
- FP-complete problems exist [@fpcomplete]:
- if L is any P-complete language (under logspace many-one reductions), then the following problem is FP-complete (under logspace parsimonious reductions): given a sequence of inputs, compute the sequence of bits indicating which of the inputs are in L

# Computational power as an effect
- in Haskell, some side effects of a computation (such as interaction with the operating system) are
  modeled as monads
- you cannot write a function f: Int -> Int, which prints something on the screen
- for this, you would need to have a function f: Int -> IO Int
- let's say a standard function of our language can be thought of
  as a fnite state transducer (finite automaton with output)
- let's say we can wrap an additional possibility of it to write something
  to a work tape in a monad. so a function of type f: Int -> WrkTp Int
  would take an int on input, return an int and also be able to
  utilize a special work memory for computation

# Strength of the type system 
- with a weak output type of a function, it's easier for us to find
  a function with satisfies it
- let's say that our type system is as strong as first-order logic
- in first-order logic, we cannot tell apart a large square from a large rectangle (proof by Ehrenfeucht–Fraïssé games)
- our function can return either of these and remain correct

# Type system vs computational model 
- this is something which I don't understand
- if we think about Turing machines, we got only one type - finite strings over a finite alphabet
- if our type system allows inductive types like Tree = Leaf | Node Tree Tree, 
  do our programs start to describe tree automata?
- intuition: type system should be strong enough so that we don't lose information
  about the computation performed
- e.g. if we don't have a type to denote Prime numbers, we might want to
  think twice before writing a function which outputs nth prime - it will
  require manual verification to use it afterwards
- the programming language should be just as strong to construct
  every ,,correct'' function (where ,,correct'' is terminating and satisfying its signature)
  and no reason for it to express more

# Implementing the interpreter 
- first problem: do our syntax really describe a tree?
- why does all of logic and proof theory look like just talking about trees?
- why is every proof a tree
- maybe not every? recent progress: Geometry of Interaction
- In proof theory, the Geometry of Interaction (GoI) was introduced by Jean-Yves Girard shortly after his work on linear logic. In linear logic, proofs can be seen as various kinds of networks as opposed to the flat tree structures of sequent calculus.
- so can syntax not be a tree?
- hint: first-order logic is compositional. does that mean that fundamentally
  it's theorems are described by a tree?

# Relation between the language and the metalanguage {.allowframebreaks}
- this is something which I don't understand
- how strong should be the metalanguage to ,,interpret'' the language considered?
- if the syntax of the language is naturally represented by a tree, we might need
  to have a tree type in the metalanguage
- strength of the type system of the metalanguage is tightly connected with
  our chosen representation of data structures used in the language
- e.g. if the language considered operates on graphs, we can pass the graph
  as an adjacency matrix, adjacency list or even a circuit which inputs a 
  node number encoded in binary and outputs its neighbors numbers as a bitmask
- what's the relation between automatas on trees to automatas on flat representations of trees (such as normal automata)
- what's the internal ,,difficulty'' of a programming language, e.g. what is the
  simplest description of computational processes modeled by the programming languages
  and the simplest interpreter, which can take this description and execute the process?

# Generation of a language vs recognizing a language {.allowframebreaks}
- can we write a solved Sudoku grid generator without writing a Sudoku backtracking solver?
- what's the ,,language'' of Sudoku? $\{1,2, \dots, n\}^{n^2}$ represents many grids which
  are obviously not valid Sudokus.
- where to look for hints? people who counted the number of valid Sudoku grids!

- finding a language for combinatorial object (e.g. Sudoku board as a tuple (param1, param2, ...)) is a   compression problem!
- In computer science, a succinct data structure is a data structure which uses an amount of space that is "close" to the information-theoretic lower bound, but (unlike other compressed representations) still allows for efficient query operations.
- every set of objects always have some ,,most natural'' description - but the definition of ,,natural''
  depends on a context and differs in different situations. when we know how to generate a language,
  it hints us what's the best formalism (paradigm) to express it. often times the paradigm
  is either logic (declarative paradigm), a generating automaton (imperative paradigm) or
  a recursive definition (functional paradigm)

# Sudoku 
- inference rules in Sudoku (so-called ,,advanced solving techniques''): do there exists
  a small set of rules, which is able to solve all of the puzzles?
- this question sounds very similar to ,,if P=/=NP, there exist infinitely many
  algorithmic techniques'' [@dawarsyntactic]

# Monads suck
- first of all: Haskell is not modeled by category theory at all! [@hasknot]
- monads are not smart! they're not any monoids in any endofunctor category
- they're a design pattern to marry computational effects with logics
- they don't have a good Curry-Howard correspondence
- there are other approaches to modeling effects: algebraic effects
- non-terminating computation breaks everything, adding a ,,bottom'' element to every type

# Inconsistencies in type systems {.allowframebreaks}
- eager lanuages don't have categorial products, lazy don't have coproducts [@eager]
- INRIA: extending type theory with forcing [@jaber:hal-00685150]. This paper presents an intuitionistic forcing translation for the Calculus of Constructions (CoC). proven to be correct by implementation in Coq. proving negation of the continuum hypothesis
- When using the Curry-Howard correspondence in order to obtain executable programs
from mathematical proofs, we are faced with a difficult problem : to interpret each axiom
of our axiom system for mathematics (which may be, for example, second order classical
logic, or classical set theory) as an instruction of our programming language. Excluded middle
can be interpreted as call/cc, catch/throw, try/with. Krivine interpreted the whole Zermelo-Fraenkel set theory axioms, but without axiom of choice. Then in ,,Dependent choice, ‘quote’ and the clock'', Krivine interprets the whole axiom of countable choice
- In this paper, we give an interpretation of the axiom of countable choice (and even the
slightly stronger axiom of dependent choice) in classical second order logic, as a programming instruction. Using the results of [11], the same method applies indeed in ZF set
theory. Our solution is to introduce a new instruction in $\lambda$-calculus, which uses an enumeration of $\lambda$-terms. We give two different computational interpretations and in fact
implementations, for this instruction : the first is similar to the quote instruction of LISP
and the second is given in terms of a clock. [@KRIVINE2003259]
- ML with call/cc operator is unsound [@mlcallcc]

- axiom of choice is derivable in constructive dependent type theory [@axiomchoice]

- [@10.1007/11417170_16] We show that a minimal dependent type theory based on $\Sigma$-types and equality is degenerated in presence of computational classical logic. By computational classical logic is meant a classical logic derived from a control operator equipped with reduction rules similar to the ones of Felleisen’s 
 or Parigot’s $\mu$ operators. As a consequence, formalisms such as Martin-Löf’s type theory or the (Set-predicative variant of the) Calculus of Inductive Constructions are inconsistent in presence of computational classical logic.


# Programming languages capturing complexity classes {.allowframebreaks}
- Kristiansen, Voda, 2005: [@10.5555/1124427.1124430] investigate two languages: an imperative and a functional one.The
computational power of fragments of these languages induce two hierarchies of complexity classes. Our first main theorem says that these hierarchies match, level by level, a complexity-theoretic alternating space-time hierarchy known from the literature. Well known complexity classes like logspace, linspace, p, pspace etc., occur in the hierarchies.
- [@mazza:LIPIcs.CSL.2015.24] We present a functional characterization of deterministic logspace-computable predicates based
on a variant (although not a subsystem) of propositional linear logic, which we call parsimonious
logic
- Bonfante [@bonfante:inria-00105744] We propose two characterizations of complexity classes by means of programming languages. The first concerns Logspace while the second leads to Ptime.
- Jones 1999 [@JONES1999151] PTIME, LOGSPACE by programming languages;
LOGSPACE is proven identical with the decision problems solvable by read-only imperative programs on Lisp-like lists; and PTIME is proven identical with the problems solvable by recursive read-only programs

# OI constraints 
- an array of length r
- an array of ints between 0 and n
- procedure will be called exactly once
- If a construction is possible, this procedure should make exactly one call to craft to report
the construction, following which it should return .
- Otherwise, the procedure should return without making any calls to craft.
- ,,it can call a function g() at most q times''
- p[i] is even
- p[i] < p[i + 1]
- ,,a 2d array is an adjacency matrix of an undirected graph''

# About non-constructivity {.allowframebreaks}
- LeetCode 1054. Distant Barcodes
- In a warehouse, there is a row of barcodes, where the ith barcode is barcodes[i].
- Rearrange the barcodes so that no two adjacent barcodes are equal. You may return any answer, and it is guaranteed an answer exists.
- Example 1: Input: barcodes = [1,1,1,2,2,2] Output: [2,1,2,1,2,1]
- Example 2: Input: barcodes = [1,1,1,1,2,2,3,3] Output: [1,3,1,3,1,2,1,2]
- what does it give us? This condition that ,,answer exists''. How to utilize it?
- 1. TFNP: In computational complexity theory, the complexity class TFNP is the class of total function problems which can be solved in nondeterministic polynomial time. That is, it is the class of function problems that are guaranteed to have an answer, and this answer can be checked in polynomial time, or equivalently it is the subset of FNP where a solution is guaranteed to exist.
- 2. PPP: Polynomial pigeonhole principle
- given a boolean circuit C having n inputs and n-1 output bits, find x=/=y such that C(x) = C(y)
- Integer factoring is probabilistically reducible to WEAKPIGEON. Can be derandomized under the assumption of the generalized Riemann hypothesis [@Je_bek_2016]


# References {.allowframebreaks}
