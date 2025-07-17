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

