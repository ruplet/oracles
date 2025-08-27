# Problems complete for deterministic logspace:
@[COOK1987385]

@article{COOK1987385,
title = {Problems complete for deterministic logarithmic space},
journal = {Journal of Algorithms},
volume = {8},
number = {3},
pages = {385-394},
year = {1987},
issn = {0196-6774},
doi = {https://doi.org/10.1016/0196-6774(87)90018-6},
url = {https://www.sciencedirect.com/science/article/pii/0196677487900186},
eprint = {https://web.archive.org/web/20161213142928/https://www.cs.utoronto.ca/~sacook/homepage/cook_mckenzie.pdf},
author = {Stephen A Cook and Pierre McKenzie},
abstract = {We exhibit several problems complete for deterministic logarithmic space under NC1 (i.e., log depth) reducibility. The list includes breadth-first search and depth-first search of an undirected tree, connectivity of undirected graphs known to be made up of one or more disjoint cycles, undirected graph acyclicity, and several problems related to representing and to operating with permutations of a finite set.}
}

# Circuit Value Problem
- For a given single-tape, polynomial-time Turing machine `M` and input `x`, in [@Kozen2006], there is an explicit construction of a boolean circuit over (0, 1, `and`, `or`, `not`) (with fan-in 2 for `and`, `or` and 1 for `not`), with one output node, such that its value is 1 if and only if machine `M` accepts input `x`. The construction is in LOGSPACE. So CVP is P-complete w.r.t. LOGSPACE-reductions.
- This is a good example of a LOGSPACE-reduction, being a good benchmark for the LF programming language and for the circuit description language
- The problem is that we can't generate tests for it; we have no database of Turing machines descriptions
- It can be implemented using topological sorting. We have code for toposort in Dafny! [@faria2023casestudiesdevelopmentverified]
- https://github.com/joaopascoalfariafeup/DafnyProjects
- We have some code here also: https://rad.ort.edu.uy/server/api/core/bitstreams/8ed3c93c-feb3-430c-8ee2-a7ec8875fc37/content 
- Toposort in WhyML: https://github.com/Ekdohibs/why3-toposort/blob/master/topo.mlw 


@Inbook{Kozen2006,
author="Kozen, Dexter C.",
title="The Circuit Value Problem",
bookTitle="Theory of Computation",
year="2006",
publisher="Springer London",
address="London",
pages="30--34",
isbn="978-1-84628-477-9",
doi="10.1007/1-84628-477-5_6",
url="https://doi.org/10.1007/1-84628-477-5_6"
}

@misc{faria2023casestudiesdevelopmentverified,
      title={Case studies of development of verified programs with Dafny for accessibility assessment}, 
      author={João Pascoal Faria and Rui Abreu},
      year={2023},
      eprint={2301.03224},
      archivePrefix={arXiv},
      primaryClass={cs.SE},
      url={https://arxiv.org/abs/2301.03224}, 
}





# Concrete Turing Machines
- How to obtain definitions of concrete Turing machines, with transitions stated explicitly etc.?
- Small deterministic Turing machines: [@KUDLEK1996241]
- Small universal Turing machines: [@ROGOZHIN1996215]
- Verified programming of Turing machines in Coq Forster: [@10.1145/3372885.3373816]
- Formalizing Turing machines: [@10.1007/978-3-642-32621-9_1]
- Ciaffaglione's proof of halt in Coq has a Turing Machine code

@article{KUDLEK1996241,
title = {Small deterministic Turing machines},
journal = {Theoretical Computer Science},
volume = {168},
number = {2},
pages = {241-255},
year = {1996},
issn = {0304-3975},
doi = {https://doi.org/10.1016/S0304-3975(96)00078-3},
url = {https://www.sciencedirect.com/science/article/pii/S0304397596000783},
author = {Manfred Kudlek}
}

@article{ROGOZHIN1996215,
title = {Small universal Turing machines},
journal = {Theoretical Computer Science},
volume = {168},
number = {2},
pages = {215-240},
year = {1996},
issn = {0304-3975},
doi = {https://doi.org/10.1016/S0304-3975(96)00077-1},
url = {https://www.sciencedirect.com/science/article/pii/S0304397596000771},
author = {Yurii Rogozhin},
abstract = {Let UTM(m, n) be the class of universal Turing machine with m states and n symbols. Universal Turing machines are proved to exist in the following classes: UTM(24,2), UTM(10,3), UTM(7,4), UTM(5,5), UTM(4,6), UTM(3,10) and UTM(2,18).}
}

@inproceedings{10.1145/3372885.3373816,
author = {Forster, Yannick and Kunze, Fabian and Wuttke, Maximilian},
title = {Verified programming of Turing machines in Coq},
year = {2020},
isbn = {9781450370974},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
url = {https://doi.org/10.1145/3372885.3373816},
doi = {10.1145/3372885.3373816},
abstract = {We present a framework for the verified programming of multi-tape Turing machines in Coq. Improving on prior work by Asperti and Ricciotti in Matita, we implement multiple layers of abstraction. The highest layer allows a user to implement nontrivial algorithms as Turing machines and verify their correctness, as well as time and space complexity compositionally. The user can do so without ever mentioning states, symbols on tapes or transition functions: They write programs in an imperative language with registers containing values of encodable data types, and our framework constructs corresponding Turing machines.  As case studies, we verify a translation from multi-tape to single-tape machines as well as a universal Turing machine, both with polynomial time overhead and constant factor space overhead.},
booktitle = {Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs},
pages = {114–128},
numpages = {15},
keywords = {Coq, Turing machines, universal machine, verification},
location = {New Orleans, LA, USA},
series = {CPP 2020}
}

@InProceedings{10.1007/978-3-642-32621-9_1,
author="Asperti, Andrea
and Ricciotti, Wilmer",
editor="Ong, Luke
and de Queiroz, Ruy",
title="Formalizing Turing Machines",
booktitle="Logic, Language, Information and Computation",
year="2012",
publisher="Springer Berlin Heidelberg",
address="Berlin, Heidelberg",
pages="1--25",
abstract="We discuss the formalization, in the Matita Theorem Prover, of a few, basic results on Turing Machines, up to the existence of a (certified) Universal Machine. The work is meant to be a preliminary step towards the creation of a formal repository in Complexity Theory, and is a small piece in our Reverse Complexity program, aiming to a comfortable, machine independent axiomatization of the field.",
isbn="978-3-642-32621-9"
}







Dowód że Cobham = PTIME jest dopiero u Tourlakis! ale też u Odifreddi!

> it's page 186 of the PDF (175 in internal numeration)  
> https://web.archive.org/web/20240103230629/http://www.piergiorgioodifreddi.it/wp-content/uploads/2010/10/CRT2.pdf  

> also, in Tourlakis 2022 (accessible on libgen)  
> George Tourlakis - Computability-Springer (2022).pdf  
> on page 625 of the PDF (608 internally), there is a proof, but also a remark about  
> this theorem, with a reference to Odifreddi's work
https://web.archive.org/web/20240121142633/https://www.cs.toronto.edu/~sacook/homepage/cobham_intrinsic.pdf


- here is code which formalizes that Cobham algebra is the same as Bellantoni and Cook's on bitstrings (as opposed to natural numbers): 
https://github.com/davidnowak/bellantonicook


Najważniejsza rzecz:
Heraud, Nowak sformalizowali algebrę BC ale na bitstringach i w Coq!
https://inria.hal.science/hal-00654217/file/itp2011-arxiv.pdf


- the whole point of using a programming language expressing a complexity class is to certify the complexity of code
- perhaps we can just certify a normal Turing Machine in Rocq?
- Yannick Forster formalized Turing Machines in Rocq
- the code for paper: https://github.com/uds-psl/tm-verification-framework
- but, from conversation with him (e-mails): this is completely impractical!
- using TMs in Rocq is just torturous
- can we formalize an interpreter of Neergaard's language?
- perhaps! I started to think about it. But gave up

- I refurbished Alberto Ciaffaglione's code 'formalizing' undecidability of halt.
- In reality, he only proved that 'Rocq cannot prove halting', not that it is unprovable in general
- I asked him for a license (e-mails), but he rarely responds.
- The code from his paper is not accessible anymore. But i have it!
- I gave a presentation about it on the seminar: https://github.com/ruplet/prezentacja-seminarium-1
- the code is also in my repo above (the repo of presentation)
- I talked with people from Undecidability library if adding his code would be of use. But it would not be! https://github.com/uds-psl/coq-library-undecidability/issues/235

- CakeML has formalized semantics. CompCert also exists.
TODO jak na teraz:
znaleźć istniejące formalizacje maszyn turinga w Coq i/lub innych weryfikatorach.
Być może formalizacja Cobhama nie będzie konieczna - być może istnieje inne,
zweryfikowane sformułowanie teorii wyrażającej dokładnie PTIME i pokazanie jej
równoważności do prawdziwych maszyn turinga.

- Heraud, Nowak 2011: A Formalization of Polytime Functions
> Characterization of PTIME on [Bit], proved formally
> We present a deep embedding of Bellantoni and Cook’s syntactic characterization of polytime functions. We prove formally that it is correct and complete with respect to the original characterization by Cobham that required a bound to be proved manually. Compared to the paper proof
by Bellantoni and Cook, we have been careful in making our proof fully contructive so that we obtain more precise bounding polynomials and more efficient translations between the two characterizations. Another difference is that we consider functions on bitstrings instead of functions on positive integers. This latter change is motivated by the application of our formalization in the context of formal security proofs in cryptography. Based on our core formalization, we have started developing a library of polytime functions that can be reused to build more complex ones.  
> https://inria.hal.science/hal-00654217/file/itp2011-arxiv.pdf

