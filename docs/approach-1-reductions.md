## Through complete problems

To show FL-completeness, it suffices to show L-completeness: FL = L* = L + NC1 reductions [@COOK19852, proposition 4.1]

- Reductions for L: e.g. first-order reductions, Immerman 1999 p.51
- USTCONN is complete for L
- a programming language for L: a finite number of variables, each <= n
- alternative: a finite number of input pointers; this is really similar to multi-head two-way automaton [@423885] [@10.1007/BF00289513]

# FO
- FO[+, *] = FO[BIT]
- FO[<, *] = FO[BIT] (Crane Beach Conjecture)
- FO[+] is less expressive than FO[<, *] = FO[<, /] = FO[<, COPRIME] [@10.1002/malq.200310041]

# DLOGTIME
- example of DLOGTIME reduction to show tree isomorphism for string-represented trees, is NC1-complete [@694595]

# NC0
- One-way permutations in NC0: [@10.1016/0020-01908790053-6]
- All sets complete under AC0 reductions are in fact already complete under NC0 reductions: [@10.1145/258533.258671] [@AGRAWAL1998127]
- Immerman at page 81 shows how to do addition in NC0 and MAJORITY in NC1 [@Immerman1998-IMMDC]
- Addition and substraction of binary numbers is in AC0: [@27676]
- This is not trivial, as these algorithms in NC0/AC0 use Chinese Remainder Representation or Fermat's Little Theorem!

# AC0
- Addition is in AC0 [@BussLectureNotes]
- FO[+, *] = DLOGTIME-uniform AC0 (https://complexityzoo.net/Complexity_Zoo:A#ac0)
- Discussion of DLOGTIME-uniform AC0: [@hella2023regularrepresentationsuniformtc0]
- Tutaj mamy definicje AC0, TC0, FATC0, FTC0 etc.: [@AGRAWAL2000395]

# TC0
- Multiplication is in TC0 [@BussLectureNotes], this resource cites this: [@doi:10.1137/0213028] but i cant find relevant info there

# NC1
- Division is in DLOGTIME-uniform NC1: [@ITA_2001__35_3_259_0]
- Reductions for NC1: Dlogtime!
- Reductions for NC1: UE* reductions; UE*-uniform NC1 = ALOGTIME [@RUZZO1981365]



# FNP class
- https://cs.stackexchange.com/questions/71617/function-problems-and-fp-subseteq-fnp
- https://cstheory.stackexchange.com/questions/37812/what-exactly-are-the-classes-fp-fnp-and-tfnp
- https://complexityzoo.net/Complexity_Zoo:F#fp

# SAT is NP-complete
- a tool can output a short witness for a 'yes' instance
- but a proof for the 'no' instance can be of exponential size!
- verified sat solver in dafny + remarks about sat solvers: https://arxiv.org/pdf/1909.01743 





importance of logspace: need language for FL to define L-reductions to prove NP-completeness!
for p-completeness, fo/ac0 reductions are used..

reductions for small classes, including
no standard notion of reductions for nc0 (maybe even for ac0)?

Dlaczego reprezentacja wejscia ma znaczenie:  
Boolean formula evaluation is only complete for LOGSPACE if input formulae are represented as graphs  
(e.g., by the list of all edges plus gate types). It was however shown in \[2\] that the problem is complete for  
NC1 under AC0-reductions if input formulae are given by their natural string encoding.  
[https://arxiv.org/pdf/1212.6567](https://arxiv.org/pdf/1212.6567)

+ dlaczego reprezentacja ma znaczenie? bo jak to lista bitow, to struktura jest uporzadkowana. jak podajemy jakies pierdolone abstrakcyjne drzewo, to nie jest uporzadkowana i logika musi byc duzo mocniejsza zeby dalej rozwiazywac nasz problem\!

Definicja first-order redukcji:  
[https://link.springer.com/book/10.1007/3-540-28788-4](https://link.springer.com/book/10.1007/3-540-28788-4)  
rozdzial 12.3

Problem, dla ktorego moc redukcji ma znaczenie:  
[https://cstheory.stackexchange.com/a/18631](https://cstheory.stackexchange.com/a/18631)  
[https://www.cse.iitk.ac.in/users/manindra/isomorphism/puniform-ac0-iso.pdf](https://www.cse.iitk.ac.in/users/manindra/isomorphism/puniform-ac0-iso.pdf)

Spoko przyklad kodowania NL subset NC2: po prostu zakoduj stconn jako matrix multiplicatoin jako problem NL-zupelny i to skompiluj do obwodu NC2: [http://www.cs.mun.ca/\~kol/courses/6743-f07/lec16.pdf](http://www.cs.mun.ca/~kol/courses/6743-f07/lec16.pdf) 






@article{10.1002/malq.200310041,
author = {Lee, Troy},
title = {Arithmetical definability over finite structures},
journal = {Mathematical Logic Quarterly},
volume = {49},
number = {4},
pages = {385-392},
keywords = {Arithmetical definability, descriptive complexity, finite model theory, Crane Beach Conjecture},
doi = {https://doi.org/10.1002/malq.200310041},
url = {https://onlinelibrary.wiley.com/doi/abs/10.1002/malq.200310041},
eprint = {https://web.archive.org/web/20250126110539/http://www1.cs.columbia.edu/~tl2383/arith.pdf},
year = {2003}
}

@INPROCEEDINGS{694595,
  author={Jenner, B. and McKenzie, P. and Toran, J.},
  booktitle={Proceedings. Thirteenth Annual IEEE Conference on Computational Complexity (Formerly: Structure in Complexity Theory Conference) (Cat. No.98CB36247)}, 
  title={A note on the hardness of tree isomorphism}, 
  year={1998},
  volume={},
  number={},
  pages={101-105},
  keywords={Tree graphs;Upper bound;Testing;Polynomials;Circuits;Jacobian matrices;Computer science;Complexity theory;Books;Turing machines},
  doi={10.1109/CCC.1998.694595},
  eprint={https://web.archive.org/web/20211202035456/https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.190/Mitarbeiter/toran/treeiso.pdf}
}

@article{10.1016/0020-01908790053-6,
author = {Hastad, Johan},
title = {One-way permutations in NC0},
year = {1987},
issue_date = {Nov 1987},
publisher = {Elsevier North-Holland, Inc.},
address = {USA},
volume = {26},
number = {3},
issn = {0020-0190},
url = {https://www.csc.kth.se/~johanh/onewaync0.pdf},
doi = {10.1016/0020-0190(87)90053-6},
journal = {Inf. Process. Lett.},
month = nov,
pages = {153–155},
numpages = {3}
}

@inproceedings{10.1145/258533.258671,
author = {Agrawal, Manindra and Allender, Eric and Impagliazzo, Russell and Pitassi, Toniann and Rudich, Steven},
title = {Reducing the complexity of reductions},
year = {1997},
isbn = {0897918886},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
url = {https://doi.org/10.1145/258533.258671},
howpublished = {https://www.cse.iitk.ac.in/users/manindra/isomorphism/puniform-ac0-iso.pdf},
doi = {10.1145/258533.258671},
booktitle = {Proceedings of the Twenty-Ninth Annual ACM Symposium on Theory of Computing},
pages = {730–738},
numpages = {9},
location = {El Paso, Texas, USA},
series = {STOC '97}
}

@article{AGRAWAL1998127,
title = {Reductions in Circuit Complexity: An Isomorphism Theorem and a Gap Theorem},
journal = {Journal of Computer and System Sciences},
volume = {57},
number = {2},
pages = {127-143},
year = {1998},
issn = {0022-0000},
doi = {https://doi.org/10.1006/jcss.1998.1583},
url = {https://www.sciencedirect.com/science/article/pii/S0022000098915835},
author = {Manindra Agrawal and Eric Allender and Steven Rudich},
abstract = {We show that all sets that are complete for NP under nonuniformAC0reductions are isomorphic under nonuniformAC0-computable isomorphisms. Furthermore, these sets remain NP-complete even under nonuniformNC0reductions. More generally, we show two theorems that hold for any complexity class C closed under (uniform)NC1-computable many–one reductions.Gap: The sets that are complete for C underAC0andNC0reducibility coincide.Isomorphism: The sets complete for C underAC0reductions are all isomorphic under isomorphisms computable and invertible byAC0circuits of depth three. Our Gap Theorem does not hold for strongly uniform reductions; we show that there are Dlogtime-uniformAC0-complete sets forNC1that are not Dlogtime-uniformNC0-complete.}
}

@book{Immerman1998-IMMDC,
	author = {Neil Immerman},
	title = {Descriptive Complexity},
	year = {1998},
      isbn = {978-1-4612-0539-5},
      url = {https://doi.org/10.1007/978-1-4612-0539-5},
	publisher = {Springer New York, NY},
      doi = {10.1007/978-1-4612-0539-5},
      pages = {81},
}


@MISC {27676,
    TITLE = {For what c is division by c in AC0?},
    AUTHOR = {daniello (https://cstheory.stackexchange.com/users/27464/daniello)},
    HOWPUBLISHED = {Theoretical Computer Science Stack Exchange},
    NOTE = {URL:https://cstheory.stackexchange.com/q/27676 (version: 2025-01-28)},
    EPRINT = {https://cstheory.stackexchange.com/q/27676},
    URL = {https://cstheory.stackexchange.com/q/27676}
}

@misc{BussLectureNotes,
  author = {Samuel Buss},
  howpublished = {https://web.archive.org/web/20220704162258/https://mathweb.ucsd.edu/~sbuss/CourseWeb/Math262A_2013F/Scribe12.pdf},
  title = {Math 262A Lecture Notes, Counting, Threshold, Vector Addition},
  year = {2014}
}


@misc{hella2023regularrepresentationsuniformtc0,
      title={Regular Representations of Uniform TC^0}, 
      author={Lauri Hella and Juha Kontinen and Kerkko Luosto},
      year={2023},
      eprint={2309.06926},
      archivePrefix={arXiv},
      primaryClass={cs.LO},
      url={https://arxiv.org/abs/2309.06926}, 
}

@article{AGRAWAL2000395,
title = {On TC0, AC0, and Arithmetic Circuits},
journal = {Journal of Computer and System Sciences},
volume = {60},
number = {2},
pages = {395-421},
year = {2000},
issn = {0022-0000},
doi = {https://doi.org/10.1006/jcss.1999.1675},
url = {https://www.sciencedirect.com/science/article/pii/S0022000099916756},
author = {Manindra Agrawal and Eric Allender and Samir Datta},
abstract = {Continuing a line of investigation that has studied the function classes #P, #SAC1, #L, and #NC1, we study the class of functions #AC0. One way to define #AC0 is as the class of functions computed by constant-depth polynomial-size arithmetic circuits of unbounded fan-in addition and multiplication gates. In contrast to the preceding function classes, for which we know to nontrivial lower bounds, lower bounds for #AC0 follow easily from established circuit lower bounds. One of our main results is a characterization of TC0 in terms of #AC0: A language A is in TC0 if and only if there is a #AC0 function f and a number k such that x∈A⇔f(x)=2|x|k. Using the naming conventions of Fenner et al. (1994, J. Comput. System Sci.48, 116–148) and Caussinus et al. (1998, J. Comput. System Sci.57, 200–212), this yieldsTC0=PAC0=C=AC0. Another restatement of this characterization is that TC0 can be simulated by constant-depth arithmetic circuits, with a single threshold gate. We hope that perhaps this characterization of TC0 in terms of AC0 circuits might provide a new avenue of attack for proving lower bounds. Our characterization differs markedly from earlier characterizations of TC0 in terms of arithmetic circuits over finite fields. Using our model of arithmetic circuits, computation over finite fields yields ACC0. We also prove a number of closure properties and normal forms for #AC0.}
}


@article{doi:10.1137/0213028,
author = {Chandra, Ashok K. and Stockmeyer, Larry and Vishkin, Uzi},
title = {Constant Depth Reducibility},
journal = {SIAM Journal on Computing},
volume = {13},
number = {2},
pages = {423-439},
year = {1984},
doi = {10.1137/0213028},
URL = {https://doi.org/10.1137/0213028},
eprint = {https://doi.org/10.1137/0213028}
}


@article{ITA_2001__35_3_259_0,
     author = {Chiu, Andrew and Davida, George and Litow, Bruce},
     title = {Division in logspace-uniform $\mbox{NC}^1$},
     journal = {RAIRO - Theoretical Informatics and Applications - Informatique Th\'eorique et Applications},
     pages = {259--275},
     publisher = {EDP-Sciences},
     volume = {35},
     number = {3},
     year = {2001},
     mrnumber = {1869217},
     zbl = {1014.68062},
     language = {en},
     howpublished = {https://www.numdam.org/item/ITA_2001__35_3_259_0/},
     url = {http://web.archive.org/web/20250115045744/http://www.numdam.org/item/ITA_2001__35_3_259_0.pdf}
}

@article{RUZZO1981365,
title = {On uniform circuit complexity},
journal = {Journal of Computer and System Sciences},
volume = {22},
number = {3},
pages = {365-383},
year = {1981},
issn = {0022-0000},
doi = {https://doi.org/10.1016/0022-0000(81)90038-6},
url = {https://www.sciencedirect.com/science/article/pii/0022000081900386},
author = {Walter L. Ruzzo},
abstract = {We argue that uniform circuit complexity introduced by Borodin is a reasonable model of parallel complexity. Three main results are presented. First, we show that alternating Turing machines are also a surprisingly good model of parallel complexity, by showing that simultaneous size/depth of uniform circuits is the same as space/time of alternating Turing machines, with depth and time within a constant factor and likewise log(size) and space. Second, we apply this to characterize NC, the class of polynomial size and polynomial-in-log depth circuits, in terms of tree-size bounded alternating TMs and other models. In particular, this enables us to show that context-free language recognition is in NC. Third, we investigate various definitions of uniform circuit complexity, showing that it is fairly insensitive to the choice of definition.}
}
