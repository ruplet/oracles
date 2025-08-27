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

# References {.allowframebreaks}


% AUTHOR = {Sylvain (https://cstheory.stackexchange.com/users/609/sylvain)},
@MISC {18919,
    TITLE = {How to minimize a FSM transducer?},
    author={sylvain},
    year = {2013},
    HOWPUBLISHED = {Theoretical Computer Science Stack Exchange},
    NOTE = {URL:https://cstheory.stackexchange.com/q/18919 (version: 2013-09-08)},
    EPRINT = {https://cstheory.stackexchange.com/q/18919},
    URL = {https://cstheory.stackexchange.com/q/18919}
}

@online{
    FSTcompositionclosed,
    author = {Daniele Micciancio},
    title = {Finite State Transducers},
    year = {2014},
    url = {https://cseweb.ucsd.edu/classes/wi14/cse105-a/LecFST.pdf},
    urldate = {2024-03-18}
}
@inproceedings{DBLP:conf/fsmnlp/Schmid05,
  author       = {Helmut Schmid},
  editor       = {Anssi Yli{-}Jyr{\"{a}} and
                  Lauri Karttunen and
                  Juhani Karhum{\"{a}}ki},
  title        = {A Programming Language for Finite State Transducers},
  booktitle    = {Finite-State Methods and Natural Language Processing, 5th International
                  Workshop, {FSMNLP} 2005, Helsinki, Finland, September 1-2, 2005. Revised
                  Papers},
  series       = {Lecture Notes in Computer Science},
  volume       = {4002},
  pages        = {308--309},
  publisher    = {Springer},
  year         = {2005},
  url          = {https://doi.org/10.1007/11780885_38},
  doi          = {10.1007/11780885_38},
  timestamp    = {Tue, 14 May 2019 10:00:53 +0200},
  biburl       = {https://dblp.org/rec/conf/fsmnlp/Schmid05.bib},
  bibsource    = {dblp computer science bibliography, https://dblp.org}
}

@misc{filiot2013twoway,
      title={From Two-Way to One-Way Finite State Transducers}, 
      author={Emmanuel Filiot and Olivier Gauwin and Pierre-Alain Reynier and Frédéric Servais},
      year={2013},
      eprint={1301.5197},
      archivePrefix={arXiv},
      primaryClass={cs.FL}
}

% AUTHOR = {Shaull (https://cs.stackexchange.com/users/6890/shaull)},
@MISC {142760,
    TITLE = {$\text{DSPACE}(O(1))=\text{REG}$ Proof?},
    author={shaull},
    year={2021},
    HOWPUBLISHED = {Computer Science Stack Exchange},
    NOTE = {URL:https://cs.stackexchange.com/q/142760 (version: 2021-07-28)},
    EPRINT = {https://cs.stackexchange.com/q/142760},
    URL = {https://cs.stackexchange.com/q/142760}
}


@online{
    kabanets,
    author = {Valentine Kabanets},
    title = {P, NP, and “search to decision” reductions},
    year = {2016},
    url = {https://www.sfu.ca/~kabanets/308/lectures/lec12.pdf},
    urldate = {2024-03-18},
}


@online{
    fpcomplete,
    author={Emil Jeřábek},
    title={Complete problems for FP},
    year={2019},
    url = {https://cstheory.stackexchange.com/questions/44484/complete-problems-for-fp#comment101108_44484},
    urldate = {2024-03-18}
}