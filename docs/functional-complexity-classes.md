# What do we mean by "P", "NP" complexity classes and why do we need "FP" and "FNP"
## Intro
23. Morioka tells that it is important to tell between decision and function complexity classes!
Cook, Nguyen shows that FAC0 is enough for reductions

## FP: p-time functional problems
- there are many definitions of FP (functional problems computable functional problems computable in polynomial time), not necessarily equivalent.
- we will use this:
- the class P consists of relations computable in polynomial time by a deterministic Turing machine (i.e. polytime relations).
- e.g. for relation IsEven, decide if IsEven(x); for relation IsConnected : {0,1}* -> {0,1}, decide IsConnected(binary description of graph G)
- the class FP consists of functions computable.. (i.e. polytime functions); source: Cook Nguyen 6.2 (characterizing P by V1)
- here we assume that some answer always exists; that the functions are total. but it doesn't make any sense from a practical
  point of view to consider partial functions; just add a designated 'bottom' element to the codomain and say that
  iff an answer does not exist, the function returns 'bottom' (=rejects / says "no" / loops forever / etc.)
- more specific definitions (Elaine Ruch, Automata, Computability and Complexity):
- A binary relation Q is in FP iff
  there is a **deterministic** polynomial-time algorithm that, given an arbitrary input x, can find some y s.t. (x, y) in Q.
- A binary relation Q is in FNP iff there is a **nondeterministic** polynomial-time ... [same as above]
- functionality in case of FP of these definitions is provided by requiring the alg. to be deterministic.
- **search** problems are defined in a similar way; given x, return any y satisfying predicate.

## An interesting class inside of FNP: TFNP
- TFNP: the class of total function problems which can be solved in nondet. ptime.
- this is a class of problems for which the decision versions make particularly little sense;
  the answer is always 'yes', but finding the witness is difficult.
- definition: TFNP is the class of function problems in FNP (defined by a relation R as above) such that R is total
- the class was first defined by Megiddo and Papadimitriou in 1989
- examples and interesting subclasses:
- PPP: subclass of TFNP problems that are guaranteed to have a solution because of the Pigeonhole Principle
- example of a problem in PPP: given a Boolean circuit {0,1}^n -> {0,1}^n, return **either** an input mapped to 0^n, **or**
  two inputs mapped to the same output
- PLS: subclass of TFNP problems that are guaranteed to have a solution because of the lemma that "every finite DAG has a sink"; formal definition at the end
- the Pigeonhole principle is interesting, because it is usually used only as a pure mathematical result. But it totally makes sense
  to consider its difficulty as a search problem (given a function from 2n elements to n elements, find collision etc.). Later,
  while talking about logics corresponding to complexity classes, we will see that if a complexity class is too weak to
  perform such a search, the corresponding logic cannot prove the theorem of pigeonhole principle. this is very interesting, as it resembles
  e.g. independence of continuum hypothesis from ZFC, but in a strictly computational setting.
- PLS will be important for us while talking about witnessing theorems. Namely, we will study how difficult should it be to
  find an actual witness `x` of a proved theorem "exists `x` s.t. phi(x)", given the proof of it (note that we operate in classical logic).
  we will find that in the setting we will introduce later, the class PLS (polynomial local search) contains the problem of searching for such a witness.

## Complete problems for functional omplexity classes
- Interestingly (at least for me), complete problems also exist for functional complexity classes.
- Circuit Value Problem is complete for P. The corresponding problem for circuits with many outputs "should" be complete for FP.
  Here, short discussion of it, including my question of stackexchange, but not including a proper proof of completeness.
  Note that we can solve CVP by topological sort, so in linear time and memory.
- So, in a way, we can conduct the "hard part"(?) of computation of any ptime problem in some super-optimized solver for CVP.
  But we don't know too much about the difficulty of the reductions; the reduction can be like O(n^3) time.


## Is P and FP not morally "the same"? Self-reducibility
- An important question we have to answer is: do we need to distinguish between P and FP, NP and FNP while studying programming languages?
- The answer is: yes. The reason is not all functional problems can be reduced to their decision counterparts.
- quote from Morioka (eccc.weizmann.ac.il/resources/pdf/morioka.pdf): Many search problems have been commonly studied indirectly using their equivalent decision counterparts. 
 For example, the complexity of finding a 3-colouring of a graph (if one exists) is studied indirectly via the problem of deciding if the input graph is 3-colourable.
  A justification for this indirect approach has been that these searhc and decision problems are polynomially equivalent, i.e. they are polynomial-time Turing reducible
  to each other. Note that functions are search problems every instance of which has a unique solution.
 However, the past research on the complexity of search problems, in particular total search problems, has shown that this indirect approach is not completely satisfactory for two reasons.
  Krentel showed in [Kre88] that the problem of computing the cost of an optimal Traveling Salesman tour of a given instance is complete for FP^{NP} while the problem of
  computing the size of a maximum clique of a graph is complete for FP^{NP}[O(log n)]. Since Krentel proves that FP^{NP} properly contains FP^{NP}[O(log n)] unless PH collapses,
 Traveling Salesman search problem apparently is harder that clique search problem, although their decision counterparts are both complete for NP.
- second reason is simple: some total search problems may not have p-equivalent decision counterparts. Evidence in this direction is obtained by Beame et. al [BCE+ 98]...
 suggest that the complete problems for PLS, PPA, PPP are unlikely to have equivalent decision problems.


## Formalities (better to skip)
- Formally, PLS = problems that can be reduced in ptime to the problem Sink-of-DAG (also called Local-Opt): given two integers n and m and two Boolean circuits
  S: {0,1}^n -> {0,1}^n s.t. S(0^n) neq 0^n; V: {0,1}^n -> {0,1, ..., 2^m-1}, find a vertex x in {0,1}^n s.t. S(x) neq x and either
  S(S(x)) = S(x) or V(S(X)) <= V(X).
