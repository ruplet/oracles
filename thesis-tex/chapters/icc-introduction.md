# Implicit Computational Complexity

## What is Implicit Computational Complexity?
Implicit Computational Complexity (ICC) is a research direction that seeks to capture complexity classes through programming language restrictions, without explicitly referring to machine models or resource bounds. Instead of measuring time or space after the fact, ICC designs languages and recursion schemes whose syntactic rules guarantee that every definable function lies within a target class - such as polynomial time or logarithmic space - while still being expressive enough to cover all functions in that class. This approach promises a principled foundation for programming languages that “build in” complexity guarantees by design. It utilizes techniques and results from mathematical logic: proof theory, recursion theory, linear logic.

ICC is often viewed as the proof-theoretic analogue of descriptive complexity. While descriptive complexity uses model-theoretic tools to classify decision problems based on their logical definability, ICC approaches computational complexity from within the syntax of programming languages and type systems.

There are two major approaches towards ICC. One is to characterize complexity classes using typed lambda calculi. The type systems in questions are often linear type systems inspired by linear logic, and are discusses later in (section: linear logic??). The other approach is to take some basic function on binary strings (e.g. `append0(x)`, `append1(x)`, `pop(x)`, `empty()`) and consider the class of functions resulting from allowing composition of functions and recursion. By seting restrictions on how the functions can be composed and how can recursive definitions look like, we can also characterize complexity classes. This approach uses recursion theory and is considered further in (section: recursion theory??).

## History of the field
The field started with consecutive results from 1991 by Leivant [@151625] and from 1992 by Bellantoni and Cook [@10.1007/BF01201998] who first provided implicit characterizations of polytime-computable functions.

Results existed before that, e.g.  
- Immerman in 1987 characterized [@doi:10.1137/0216051] polytime *relations* in a way that doesn't involve any explicit size bounds in the defining expressions.  
- Compton and LaFlamme in 1990 [@COMPTON1990241] characterized uniform $\text{NC}^1$. Allen in 1991 [@ALLEN19911] characterized uniform $\text{NC}$. Their works were unsatisfactory due to relying on explicit polynomial bounds, more or less hidden in the definitions. Moreover, they have also only considered *relations* or *decisive* complexity classes (e.g. $\text{PTIME}$) and not *functions* computable in these complexities ($\text{FPTIME}$). But e.g. the exponential relation  $E(x, y) \iff y = 2^x$ is polytime to decide.  
- There has been some related work on characterizations of polytime functions, e.g. of Gurevich from 1983 [@4568079], and the foundational work by Cobham from 1964 [@Cobham1964-COBTIC], but their approaches still contained explicit polynomial bounds in some form, more or less hidden in the definition.  

For a more comprehensive literature review of the origins of this area, please see [@bloch1994function]

Since 1990's, an abundance of complexity classes have been characterized implicitly, most important of them have been characterized in a variety of ways, see e.g. [@NIGGL201047] for an overview of characterizations of $\text{FPTIME}$ and $\text{FNC}$, or [@10.1016/j.ic.2015.12.009] for two different function algebras capturing the $\text{NC}^k$ hierarchy.

More importantly for us, in 1999 Neil D. Jones published how fragments of the Lisp language correspond to L and P *decisive* complexity classes [@JONES1999151]. Bonfante in 2006, expanding on Jones' work, published his characterizations of the same two classes [@10.1007/11784180_8]. Kristiansen and Voda in 2005 [@kristiansenvoda2005] study an imperative and a functional programming language, fragments of which induce hierarchies of complexity classes, with well-known complexity classes such as LOGSPACE, LINSPACE, P, PSPACE (also: decisive) occuring in the hierarchies. Other characterizations include works of Kristiansen [@kristiansen2005neat], Oitavem [@Oitavem+2010+355+362] and many more.

As the most important classes for the scope of this thesis are FPTIME and FLOGSPACE, we discuss their characterizations separately in the following sections.

A good introduction to Implicit Computational Complexity is there:
Simone Martini's presentation: part 1 [@martini2006implicit1], part 2 [@martini2006implicit2] and part 3 [@martini2006implicit3]. Also, Simona Ronchi Della Rocca's presentation from 2019: [@ronchi2019logic] and 
Ugo Dal Lago's Short Introduction to ICC from 2012 [@DalLago2012].