# Implicit Computational Complexity

Implicit Computational Complexity (ICC) is a research direction that seeks to capture complexity classes through programming language restrictions, without explicitly referring to machine models or resource bounds. Instead of measuring time or space after the fact, ICC designs languages and recursion schemes whose syntactic rules guarantee that every definable function lies within a target class - such as polynomial time or logarithmic space - while still being expressive enough to cover all functions in that class. This approach promises a principled foundation for programming languages that “build in” complexity guarantees by design. It utilizes techniques and results from mathematical logic: proof theory, recursion theory, linear logic.

The field started with consecutive results from 1991 by Leivant [@151625] and from 1992 by Bellantoni and Cook [@10.1007/BF01201998] who first provided implicit characterizations of polytime-computable functions.

Results existed before that, e.g.  
- Immerman in 1987 characterized [@doi:10.1137/0216051] polytime *relations* in a way that doesn't involve any explicit size bounds in the defining expressions.  
- Compton and LaFlamme in 1990 [@COMPTON1990241] characterized uniform $\text{NC}^1$. Allen in 1991 [@ALLEN19911] characterized uniform $\text{NC}$. Their works were unsatisfactory due to relying on explicit polynomial bounds, more or less hidden in the definitions. Moreover, they have also only considered *relations* or *decisive* complexity classes (e.g. $\text{PTIME}$) and not *functions* computable in these complexities ($\text{FPTIME}$). But e.g. the exponential relation  $E(x, y) \iff y = 2^x$ is polytime to decide.  
- There has been some related work on characterizations of polytime functions, e.g. of Gurevich from 1983 [@4568079], and the foundational work by Cobham from 1964 [@Cook_1970], but their approaches still contained explicit polynomial bounds in some form, more or less hidden in the definition.  

Since 1990's, an abundance of complexity classes have been characterized implicitly, e.g. PSPACE [@gaboardi2010implicitcharacterizationpspace] and $\text{PP}$ [@dallago_et_al:LIPIcs.MFCS.2021.35]. Many classes have been characterized in a variety of ways, see e.g. [@NIGGL201047] for an overview of characterizations of $\text{FPTIME}$ and $\text{FNC}$, or [@10.1016/j.ic.2015.12.009] for two different function algebras capturing the $\text{NC}^k$ hierarchy..
Some of the studied complexity classes remain notoriously difficult to be characterized implicitly, most notably BPP,
some characterization of which were however studied in [@lago2012higherordercharacterizationprobabilisticpolynomial].

As the most important classes for the scope of this thesis are PTIME and LOGSPACE (the classes most commonly used for
writing reductions in complexity theory), we devote separate sections for their characterizations.

A good introduction to Implicit Computational Complexity is there:
Simone Martini's presentation: part 1 [@martini2006implicit1], part 2 [@martini2006implicit2] and part 3 [@martini2006implicit3]. Also, Simona Ronchi Della Rocca's presentation from 2019: [@ronchi2019logic] and 
Ugo Dal Lago's Short Introduction to ICC from 2012 [@DalLago2012].


## LOGSPACE

- Neil D. Jones: Computability and Complexity From a Programming Perspective
- complexity of while programs, charcterization of logspace and ptime by goto programs

- linear and other time hierarchies for while programs etc.
> http://hjemmesider.diku.dk/~neil/comp2book2007/book-whole.pdf