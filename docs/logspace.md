- Cobham 1973: characterizes PTIME with explicit bounds
> But his characterization sucks, it has an explicit bound  
> https://www.cs.toronto.edu/~sacook/homepage/cobham_intrinsic.pdf

- Lind, Meyer 1973: A characterization of log-space computable functions
> This paper sucks, requires explicit bound on output size (log-bounded recursion on notation)  
> https://dl.acm.org/doi/pdf/10.1145/1008293.1008295

- Murawski, Ong 2004: define BC- class
> https://core.ac.uk/download/pdf/82378545.pdf

- Schopp: historia LOGSPACE
> https://ulrichschoepp.de/Docs/csl06.pdf

- Lind characterizes FLOGSPACE (1974)
> the paper sucks! log-bounded recursion!
> https://dspace.mit.edu/handle/1721.1/148880

- A programming language for PP
> https://drops.dagstuhl.de/storage/00lipics/lipics-vol202-mfcs2021/LIPIcs.MFCS.2021.35/LIPIcs.MFCS.2021.35.pdf

- Cloute, Takeuti: Recursion-theoretic characterization of complexity classes
> AC0(2), AC0(6), Flogspace - also with explicit bounds!
> page 163 pdf: https://link.springer.com/chapter/10.1007/978-1-4612-2566-9_6

- Niggl, Wunderlich 2010: Implicit characterizations of FPTIME and NC revisited
> Cob = FPTIME
> From a programming point of view, function algebras like Cob are not practically appealing because they cannot be used as
a construction kit: Whenever a recursion is performed, one is prompted with a proof that the computed function is bounded
by some function already constructed.
Building on work of Simmons [25] and Leivant [15,16], Bellantoni and Cook [4] were the first to give a purely functional
characterization of FPTIME that does away with the “explicit” reference to the growth rate of functions defined by (BRN) in
Cobham’s class. In fact, this “explicit” reference can be made “implicit” by ensuring the following principle (P-BC): Computed
values in recursions must not control other recursions (cf. [20,22]).
That principle led to the well-known function algebra BC [4] which actually can be used as a construction kit, since all
restrictions are of purely syntactical nature. 
> https://www.sciencedirect.com/science/article/pii/S1567832609000113

- Gaboardi 2010: An implicit characterization of PSPACE
> https://arxiv.org/pdf/1006.0030.pdf

- Bellantoni and Cook: A new recursion-theoretic characterization of the polytime functions
> https://www.cs.utoronto.ca/~sacook/homepage/ptime.pdf

- Isabel Oitavem 2010: Logspace without bounds
> provides recursion-theoretic characterization of FLOGSPACE, similar to Clote and Takeuti  
> these have explicit bounds in the recursion schemes: Cobham: FP, Thompson: PSPACE, Clote and Takeuti: NC, LOGSPACE  
> https://www.degruyter.com/document/doi/10.1515/9783110324907.355/html

- A Functional Language for Logarithmic Space, Neergaard 2004
> https://link.springer.com/chapter/10.1007/978-3-540-30477-7_21

- Ulrich Schopp 2006: Space-efficient Computation by Interaction
> https://ulrichschoepp.de/Docs/seci.pdf

- Neil D. Jones: Computability and Complexity From a Programming Perspective
> http://hjemmesider.diku.dk/~neil/comp2book2007/book-whole.pdf

- Neil D. Jones: LOGSPACE and PTIME characterized by programming languages
> https://core.ac.uk/download/pdf/82651296.pdf

- Bonfante: Some programming languages for LOGSPACE and PTIME
> https://inria.hal.science/inria-00105744/document

- Martin Hofmann: Programming Languages for Logarithmic Space 2006
> https://www-lipn.univ-paris13.fr/~baillot/GEOCAL06/SLIDES/Hofmann1302.pdf

- Kristiansen, Voda 2005: languages for LOGSPACE, LINSPACE, P, PSPACE etc.
> https://www.researchgate.net/publication/220673222_Programming_Languages_Capturing_Complexity_Classes

- Kristiansen: Neat function algebraic characterizations of logspace and linspace
> https://link.springer.com/article/10.1007/s00037-005-0191-0

- Heraud, Nowak 2011: A Formalization of Polytime Functions
> Characterization of PTIME on [Bit], proved formally
> We present a deep embedding of Bellantoni and Cook’s syntactic characterization of polytime functions. We prove formally that it is correct and complete with respect to the original characterization by Cobham that required a bound to be proved manually. Compared to the paper proof
by Bellantoni and Cook, we have been careful in making our proof fully contructive so that we obtain more precise bounding polynomials and more efficient translations between the two characterizations. Another difference is that we consider functions on bitstrings instead of functions on positive integers. This latter change is motivated by the application of our formalization in the context of formal security proofs in cryptography. Based on our core formalization, we have started developing a library of polytime functions that can be reused to build more complex ones.  
> https://inria.hal.science/hal-00654217/file/itp2011-arxiv.pdf

- Neil D. Jones: Cons-free Programs and Complexity Classes between LOGSPACE and PTIME
> https://arxiv.org/pdf/2008.02932

- Term rewriting characterisation of LOGSPACE for finite and infinite data
> https://www.mimuw.edu.pl/~lukaszcz/logspace.pdf

- single-valued aperiodic nondeterministic finite-state transducers = FO reductions
> The Descriptive Complexity Approach to LOGCFL
> https://arxiv.org/abs/cs/9809114

- Critique of Cobham's paper
> there is nothing in this paper, really  
> additionally, it's difficult to access:  
> https://web.archive.org/web/20240121142633/https://www.cs.toronto.edu/~sacook/homepage/cobham_intrinsic.pdf  
> here, you can see the review of the above, written by Cook  
> https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/alan-cobham-the-intrinsic-computational-difficulty-of-functions-logic-methodology-and-philosophy-of-science-proceedings-of-the-1964-international-congress-edited-by-yehoshua-barhillel-studies-in-logic-and-the-foundations-of-mathematics-northholland-publishing-company-amsterdam-1965-pp-2430/475D96633FB147B7C78B1FCCE3A7B053?utm_campaign=shareaholic&utm_medium=copy_link&utm_source=bookmark  
> and in this review you can see that Cobham only hypothesises that his algebra expresses P  
> his algebra is:  
> L = PTIME = the least class of functions including the eleven functions s_i(x) = 10x + i, i=0,1,...,9 and x^{l(y)} (where l(y) is the decimal length of y), and closed under the operations of explicit transformation, composition, and limited recursion on notation (digit-by-digit recursion).  
> And he doesn't have the proof that his L (it's not logspace) is really equal to P.  
> Here is the proof of the above, though:  
> https://web.archive.org/web/20240103230629/http://www.piergiorgioodifreddi.it/wp-content/uploads/2010/10/CRT2.pdf  
> it's page 186 of the PDF (175 in internal numeration)  
> also, in Tourlakis 2022 (accessible on libgen)  
> George Tourlakis - Computability-Springer (2022).pdf  
> on page 625 of the PDF (608 internally), there is a proof, but also a remark about  
> this theorem, with a reference to Odifreddi's work

- About BCe- algebra; Space-efficiency and the Geometry of Interaction, Ulrich Schopp
> About programming languages capturing logarithmic space
> https://www-lipn.univ-paris13.fr/~baillot/GEOCAL06/SLIDES/Schoepp.pdf