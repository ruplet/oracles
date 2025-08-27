# Implicit Computational Complexity

Implicit Computational Complexity (ICC) is a research direction that seeks to capture complexity classes through programming language restrictions, without explicitly referring to machine models or resource bounds. Instead of measuring time or space after the fact, ICC designs languages and recursion schemes whose syntactic rules guarantee that every definable function lies within a target class - such as polynomial time or logarithmic space - while still being expressive enough to cover all functions in that class. This approach promises a principled foundation for programming languages that “build in” complexity guarantees by design. It utilizes techniques and results from mathematical logic: proof theory, recursion theory, linear logic.

The field started with consecutive results from 1991 by Leivant [@151625] and from 1992 by Bellantoni and Cook [@10.1007/BF01201998] who first provided implicit characterizations of polytime-computable functions.

Results existed before that, e.g.  
- Immerman in 1987 characterized [@doi:10.1137/0216051] polytime *relations* in a way that doesn't involve any explicit size bounds in the defining expressions.  
- Compton and LaFlamme in 1990 [@COMPTON1990241] characterized uniform $\text{NC}^1$. Allen in 1991 [@ALLEN19911] characterized uniform $\text{NC}$. Their works were unsatisfactory due to relying on explicit polynomial bounds, more or less hidden in the definitions. Moreover, they have also only considered *relations* or *decisive* complexity classes (e.g. $\text{PTIME}$) and not *functions* computable in these complexities ($\text{FPTIME}$). But e.g. the exponential relation  $E(x, y) \iff y = 2^x$ is polytime to decide.  
- There has been some related work on characterizations of polytime functions, e.g. of Gurevich from 1983 [@4568079], and the foundational work by Cobham from 1964 [@Cook_1970], but their approaches still contained explicit polynomial bounds in some form, more or less hidden in the definition.  
For an exhaustive literature review of the origins of this area, please see [@bloch1994function]

Since 1990's, an abundance of complexity classes have been characterized implicitly, e.g. PSPACE [@gaboardi2010implicitcharacterizationpspace] and $\text{PP}$ [@dallago_et_al:LIPIcs.MFCS.2021.35]. Many classes have been characterized in a variety of ways, see e.g. [@NIGGL201047] for an overview of characterizations of $\text{FPTIME}$ and $\text{FNC}$, or [@10.1016/j.ic.2015.12.009] for two different function algebras capturing the $\text{NC}^k$ hierarchy.

Notably, in 1999 Neil D. Jones published how fragments of the Lisp language correspond to L and P decisive complexity classes [@JONES1999151]. Bonfante in 2006, expanding on Jones' work, published his characterizations of the same two classes [@10.1007/11784180_8]. Kristiansen and Voda in 2005 [@kristiansenvoda2005]. Martin Hoffman presented an overview of languages for LOGSPACE in 2006: [@hofmann2006logspace]. Kristiansen in 2005 characterize logspace and linspace: [@kristiansen2005neat] Oitavem [@Oitavem+2010+355+362]


Some of the studied complexity classes remain notoriously difficult to be characterized implicitly. One example is BPP,
a characterization of which was however studied in [@lago2012higherordercharacterizationprobabilisticpolynomial]. But
more importantly, the class `inv-P` of graph permutation-invariant problems decidable in polynomial time, is conjectured
to not be characterizable this way. This is a restatement of the problem of finding a "logic capturing PTIME on unordered structures". A good discussion of this problem is present in Anuj Dawar's presentation from 2012: [@dawar2012syntactic].

As the most important classes for the scope of this thesis are PTIME and LOGSPACE (the classes most commonly used for
writing reductions in complexity theory), we devote separate sections for their characterizations.

A good introduction to Implicit Computational Complexity is there:
Simone Martini's presentation: part 1 [@martini2006implicit1], part 2 [@martini2006implicit2] and part 3 [@martini2006implicit3]. Also, Simona Ronchi Della Rocca's presentation from 2019: [@ronchi2019logic] and 
Ugo Dal Lago's Short Introduction to ICC from 2012 [@DalLago2012].


## Recursion theory, Bellantoni and Cook's BC algebra, LOGSPACE

Lind 1973 [@10.1145/1008293.1008295], 1974 [@lind1974logspace] : function algebra, explicit resource bounds
function algebra with unary numbers [@10.1007/BF01201998]
tail recursive readonly programs [@JONES1999151]

Murawski and Ong in 2000 introduce BCminus [@murawski2000can], [@MURAWSKI2004197].
in 2004 moller-neergaard prove bce- = fl


history of logspace: [@schoepp2006spaceefficiency]

- I have obtained the code from the author, refurbished it (ported from Moscow ML to SML/NJ) and found a second, unpublished paper that clarifies a lot in the original paper
- code for Neergaard is there: https://github.com/ruplet/neergaard-logspace-characterization
- for Neergaard, I also have a proof that the function `shiftR` from his published paper is not implementable (typo, need to reverse arguments). The proof is already in `thesis-tex/main.tex`, not copying it here
- I thought for a while if a port of Neergaard's code to a modern implementation of ML would be of use. I ended up just porting to SML/NJ, as it is relatively easy to install (instructions from modern linux: https://github.com/spamegg1/unix-sml)
- https://cakeml.org/ CakeML is very interesting. It has formalized semantics and wins many awards! In particular, at POPL 2024, the paper from POPL 2014 that introduced CakeML, received the Most Influential POPL Paper Award! But I gave up on porting Neergaard's code to CakeML.
- Some links to documentation of **the** version of SML used; I needed them to modify Neergaard's code:
- https://smlfamily.github.io/Basis/array.html#SIG:ARRAY.foldri:VAL
- https://www.cs.princeton.edu/~appel/smlnj/basis/array.html
- https://www.cs.princeton.edu/~appel/smlnj/basis/aggregates-chapter.html#array-vector-slice
- https://smlfamily.github.io/Basis/vector.html#SIG:VECTOR.mapi:VAL
- SML online: https://sosml.org/editor?0&


- we have just a tiny bit of Haskell code written by me to define Neergaard's language and re-write the function proposed in his paper into working, formal implementations in this folder (app/ subdirectory) 

- koncepcja: różnica między algebrą BCeps- a BC jest taka, że BCeps- "wymaga"
  re-obliczania podwyrażeń po zrobieniu na nich ifa. To jest insight za L neq P

```hs
identity :: Func
identity = Proj 1 0 1

oneNormalToZero :: Func
oneNormalToZero =
  let g = ZeroFunc in
  let h = Proj 1 1 2 in
  let d = identity in
  Recursion 0 0 g h h d d

-- Proposition 1. Let m and n by numbers in binary. Right shift shiftR(m : n) of
-- m by |n| and selection of bit |n| from m are definable in BCε.

-- shiftR(n : m) = m >> |n|
shiftR :: Func
shiftR =
  let g = Proj 0 1 1 in
  let d = oneNormalToZero in
  -- h(timer : recursive) = tail(recursive)
  let h = Composition 0 1 1 [1] Tail [] [Proj 1 1 2] in
  Recursion 0 1 g h h d d
```


## Linear logic

also was used for logspace, e.g. for characterization of logspace-computable predicates, a variant of propositional linear logic called "parsimonious logic" was introduced in [@mazza:LIPIcs.CSL.2015.24].

- we have an interpreter and examples for the programming language invented by Ugo dal Lago and Ulrich Schopp (based on linear logic) there: https://github.com/uelis/IntML