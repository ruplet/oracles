## Implicit Computational Complexity

Implicit Computational Complexity (ICC) is a research direction that seeks to capture complexity classes through programming language restrictions, without explicitly referring to machine models or resource bounds. Instead of measuring time or space after the fact, ICC designs languages and recursion schemes whose syntactic rules guarantee that every definable function lies within a target class—such as polynomial time or NC—while still being expressive enough to cover all functions in that class. This approach promises a principled foundation for programming languages that “build in” complexity guarantees by design.

For decades, researchers in computational complexity have sought ways to characterize complexity classes without relying on Turing machines or other low-level models of computation. One of the earliest successes came from Cobham (1965), who described the class of polynomial-time computable functions as those generated from a small set of basic functions by closure under composition and a restricted form of recursion. This foundational result was later simplified and refined by Bellantoni and Cook (1992), whose techniques removed the need for explicit time bounds and instead enforced complexity constraints through the syntactic structure of functions.

Following Cobham’s work, many recursion-theoretic and logical characterizations were developed for other complexity classes. Examples include Lind’s (1974) characterization of logspace, Allen’s (1991) characterization of NC, and Compton and LaFlamme’s (1990) and Clote’s (1989, 1993) results for uniform NC¹, AC⁰, and related parallel classes. While these approaches provided deep insights, they often relied on explicit polynomial bounds, artificially restricted recursion depths, or specially chosen base functions with growth rates tailored to the target complexity class.

A major step toward elegance came with the introduction of *tiered recursion*, independently proposed by Leivant (1990) and Bellantoni and Cook (1992). In this approach, function parameters are syntactically divided into *safe* (tier 0) and *normal* (tier 1) arguments, depending on how they influence computation. Safe arguments are used only for local, constant-time operations, while normal arguments may control recursion or iteration. This syntactic distinction enforces complexity bounds implicitly, avoiding the need for explicit size or depth constraints, while still allowing expressive and efficient function definitions.

In this thesis, we apply the tiered recursion technique to characterize parallel complexity classes. Specifically, we replace the “recursion on notation” used in Cobham’s and Bellantoni–Cook’s frameworks with a *divide-and-conquer recursion* scheme. Without tiering, divide-and-conquer recursion has appeared in the work of Buss (1986), Compton and LaFlamme (1990), and Allen (1991), but only in combination with manually imposed bounds. With tier discipline, these bounds emerge naturally from the recursion structure itself, leading to simpler and more principled characterizations.

This perspective forms the foundation for our investigation into implicit computational complexity as a method for designing programming languages that inherently enforce resource bounds.



- Simone Martini: On Implicit Computational Complexity
> https://www.cs.unibo.it/~martini/BISS/martini-1.pdf  
> https://www.cs.unibo.it/~martini/BISS/martini-2.pdf  
> https://www.cs.unibo.it/~martini/BISS/martini-3.pdf  
> https://www.cs.unibo.it/~martini/BISS/  

- Simona Ronchi Della Rocca 2019: Logic and Implicit Computational Complexity
> http://panhellenic-logic-symposium.org/12/slides/Day1_Ronchi.pdf  


open problem: an implicit characterization of parimonious reductions

Najwazniejsi badacze:
Isabel Oitavem
Ugo Dal Lago

kolejna characteryzacja FPTIME, NC:
Implicit characterizations of FPTIME and NC revisited

Two function algebras defining functions in NC^k
 boolean circuits


- A programming language for PP
> https://drops.dagstuhl.de/storage/00lipics/lipics-vol202-mfcs2021/LIPIcs.MFCS.2021.35/LIPIcs.MFCS.2021.35.pdf

- Gaboardi 2010: An implicit characterization of PSPACE
> https://arxiv.org/pdf/1006.0030.pdf

- Bellantoni and Cook: A new recursion-theoretic characterization of the polytime functions
> https://www.cs.utoronto.ca/~sacook/homepage/ptime.pdf

- Neil D. Jones: Computability and Complexity From a Programming Perspective
- complexity of while programs, charcterization of logspace and ptime by goto programs
- linear and other time hierarchies for while programs etc.
> http://hjemmesider.diku.dk/~neil/comp2book2007/book-whole.pdf

